# Arity-annotated values and the fast apply-n path

*A research note on self-optimising evaluation for a Lean 4 kernel.*

## 1. Setting

`zignodamus` type-checks Lean 4 by **normalisation by evaluation** (NbE): terms are
compiled into a semantic domain of *values* (`src/value.zig`), reduced to weak head
normal form (WHNF) on demand, and compared by a conversion checker
(`src/conv.zig`). The values are "WHNF-like": each one exposes only its outermost
constructor — a `lam`, a `pi`, a neutral `rigid`/`unfold` head with a spine of
eliminators, a literal — and defers everything underneath behind closures and
thunks.

Two observations motivate this note, both borrowed from how *compilers* and
*self-optimising runtimes* work.

### 1.1 Self-optimisation is already the house style

The kernel is full of data structures that *get better as the program runs* rather
than being optimised ahead of time:

- The positive half of the conversion cache is a **disjoint-set / union-find**
  (`src/union_find.zig`, used as `TcCache.value_eq`). Every time two values are
  proven definitionally equal they are `unite`d; subsequent equality queries are
  answered in near-constant time, and *path compression* means the structure
  literally rewrites itself to be flatter on each `find`. This is the
  self-optimising, disjoint-set idea the task points at — and it is load-bearing.
- **Glued evaluation** and the `unfold`/`forced` memo cells let a definition keep
  both its folded and unfolded forms, unfolding lazily and caching the result on
  the value itself.
- A dozen `swiss_map` memo tables (`open_eval_cache`, `iota_cache`,
  `rec_rule_cache`, `type_cache`, …) turn repeated work into hash lookups.

In other words the kernel is already a *JIT-flavoured* interpreter: a program that
optimises itself while it runs. The question this note asks is whether the *shape*
of a value — specifically the **arity of a function** — is a further piece of
"profile" we can exploit, the way a method-JIT specialises a call site once it
knows the callee's shape.

### 1.2 Not every arrow deserves the same algorithm

The evaluator's hottest primitive is application. In a naïve NbE core, applying a
function to *n* arguments is *n* independent β-steps, each of which:

1. extends the environment with one argument,
2. evaluates the body one binder deeper, and
3. **materialises an intermediate closure value** — a *partial application* (PAP)
   in the terminology of functional-language back ends — that is immediately
   consumed by the next β-step.

For a definition like `Nat.rec`'s minor premise, or any curried combinator, the
value being applied is a *deep* lambda: `λ p m₀ … mₖ … . body`. Saturating it one
argument at a time allocates and caches k−1 throwaway PAPs. That is exactly the
inefficiency that the **eval/apply** model of Marlow & Peyton Jones was designed to
remove [1]: if the caller knows the callee's **arity**, it can push all the
available arguments in one move and jump straight to the saturated body, never
building the intermediate PAPs.

So we annotate the WHNF value with its arity and give the evaluator an *apply-n*
path — a fast `apply2`/`apply3`/…/`apply-k` — instead of treating every arrow as a
single-argument β-redex.

## 2. The annotation

The arity of a lambda value is a purely *syntactic* property of its (interned)
body expression: the number of directly nested `.lambda` binders at its head. It
does not depend on the environment, so it is computed once and memoised:

```zig
// src/eval.zig
fn leadingLambdas(self, e: ExprPtr) u32   // cached in TcCache.arity_cache : ExprPtr → u32
pub fn lamArity(self, v: V) u32           // = 1 + leadingLambdas(body-under-first-binder)
```

Because expressions are hash-consed, the annotation is shared across *every*
closure built over the same body — one lambda term contributes one cache entry no
matter how many times it is instantiated. This is the value-level analogue of a
compiler recording a function's arity in its info table.

## 3. The fast path

`applyMany(f, args)` folds an argument vector into `f`. When the head is a lambda,
the annotation says how many arguments the binder chain can absorb, and the whole
run of β-redexes is discharged with **one** environment-extension chain and **one**
`eval` of the innermost body:

```zig
pub fn applyMany(self, depth, f0, args) V {
    var f = f0; var i = 0;
    while (i < args.len) {
        if (f.* != .lam) { f = apply(self, depth, f, args[i]); i += 1; continue; }
        const clo  = f.lam.body;
        const take = @min(lamArity(self, f), args.len - i);   // arity-driven apply-n
        var e = envExtend(clo.env, args[i]);
        var body = clo.body();
        var k = 1;
        while (k < take) : (k += 1) {
            const pruned = keyEnv(self, e, body); // exactly what eval would store in the PAP's closure
            e = envExtend(pruned, args[i + k]);
            body = body.lambda.body;
        }
        i += take;
        f = eval(self, depth, e, body);           // one eval, no intermediate PAP values
    }
    return f;
}
```

When fewer arguments are available than the arity (`take < arity`), the final
`eval` naturally produces the correct partial application, so under-application
still works and remains cached.

### 3.1 Where it is used

`applyMany` replaces the one-argument `apply` folds on the paths where a freshly
built value is saturated against a *known argument vector* — precisely the places
the deep-lambda pattern occurs:

- **ι-reduction / recursor firing** (`fireRecursor`, `natRecNatlit`): the recursor
  rule value is a deep lambda over params, motives, minor premises and the
  constructor's own fields.
- **Definition unfolding** (`unfoldValueGo`): a definition body applied to its
  spine; runs of application eliminators are batched and flushed only at a
  projection.
- **Quotient lifting** (`fireQuot`).

The general `eval` application path is deliberately *left untouched*: it recurses
so that it can cache every application *prefix* in `open_eval_cache` (valuable when
`f a` is shared between `f a b` and `f a c`). `applyMany` is applied only where
prefixes are not shared and the allocation saving dominates — the same
eval/apply-vs-push/enter trade-off discussed in [1].

## 4. Correctness

`applyMany` is a *transparent* refactor of "fold `apply`": each intermediate binder
threads the environment through `keyEnv` exactly as `eval`'s `.lambda` case does
before storing it in a PAP's closure, so the environment object handed to the final
`eval` is *identical* to the one the one-at-a-time fold would have built. The only
difference is that the intermediate PAP *values* are never allocated or inserted
into `open_eval_cache`. `src/bench_apply.zig` checks this directly: for a grid of
curried selectors it asserts that `applyMany` agrees **pointer-for-pointer** with
the `apply` fold and selects the de Bruijn-named argument, including the
partial-application split case and the >64-loose-bvar environment path.

## 5. Measurement

A self-contained microbenchmark (`src/bench_apply.zig`, ReleaseFast) saturates a
32-ary curried lambda, clearing the evaluation caches each iteration so real
reduction is measured rather than memoisation. Each strategy runs on its own fresh
value arena (otherwise the second-run strategy inherits the first's arena bloat and
the comparison inverts — a cautionary tale about benchmark hygiene):

```
apply-n microbench (k=32, 4000 iters, best of 5):
  apply-fold 15.4 ms, applyMany 7.7 ms  (≈2.0x speedup)
```

Run it with:

```
zig test -OReleaseFast -lc src/root.zig \
  --cache-dir .zig-cache --global-cache-dir $(zig env | ...) --zig-lib-dir <lib>
# or simply: zig build test   (Debug skips the timing test; correctness runs)
```

### Caveats — read before believing

- This is a **best-case microbenchmark**: a fully saturated, maximally deep lambda
  with no useful prefix sharing. It isolates the mechanism; it is *not* an
  end-to-end kernel result.
- The real-world win is proportional to how much a proof's reduction is dominated
  by saturating multi-binder lambdas (recursor rules, definition bodies). A term
  that is mostly neutral spine-building, or whose lambdas are already unary, sees
  little change — `applyMany` degrades to `apply` on the non-lambda head.
- An honest end-to-end number needs the author's Mathlib harness (the
  instruction-count methodology in the README). The change is designed to be
  conservative there: it never does *more* work than the fold, only ever *less*
  (fewer PAP allocations and cache operations), and the general prefix-caching
  `eval` path is unchanged.

## 6. Where this goes next

The arity annotation is a small lever with more to pull:

1. **Arity on function *types* for spine typing.** `spineType` /
   `spineTypeWithValue` re-force the function type at every argument. A
   non-dependent prefix of a Π-telescope could be consumed in one step; the arity
   of the *type* tells you how long that prefix is.
2. **Arity-indexed neutral heads.** Annotating a `rigid` recursor head with "args
   needed before ι can fire" lets `apply` skip the `spineApps` allocation and the
   reduction attempt while a recursor is still under-applied — a cheap, purely
   additive short-circuit.
3. **True JIT specialisation of hot recursors.** The disjoint-set/self-optimising
   theme, taken further: compile a frequently fired `RecRule` into a specialised
   closure (a `apply-k` tailored to that constructor's telescope), the value-level
   analogue of a tracing JIT compiling a hot loop.
4. **Push/enter for neutral spines.** `applyMany` already batches application
   eliminators when unfolding; the same batching could be threaded through spine
   construction to cut hash-cons traffic on `spineSnocHc`.

Each of these keeps to the same principle: let the value's *exposed shape* — its
arity — pick the specialised algorithm, instead of running one generic β-loop over
every arrow.

## References

[1] Simon Marlow and Simon Peyton Jones. *Making a fast curry: push/enter vs.
    eval/apply for higher-order languages.* Journal of Functional Programming,
    16(4–5):415–449, 2006. (Earlier: ICFP 2004.)

[2] András Kovács. *smalltt* — notes on glued evaluation and approximate
    conversion checking. <https://github.com/AndrasKovacs/smalltt>

[3] Robert E. Tarjan. *Efficiency of a good but not linear set union algorithm.*
    Journal of the ACM, 22(2):215–225, 1975. (Union-find with path compression —
    the self-optimising structure behind the conversion cache.)
