# Lean kernel

This is a type checker (kernel) for the [Lean 4](https://lean-lang.org) programming language and theorem prover.

It uses normalisation by evaluation, unlike the official kernel, which uses a locally closed representation, and substitution.

It is based on the previous (partially) NbE type checker https://github.com/intgrah/sokonanoda, which is itself a fork of https://github.com/SchrodingerZhu/still-nanoda, which is itself a fork of https://github.com/ammkrn/nanoda_lib.

## Soundness

The type checker has not yet had enough scrutiny so you should not use it for serious purposes.

## Performance

This type checker was kind of optimised for the [Lean kernel arena](https://arena.lean-lang.org/), so there are some optimisations in place that might be seen as "cheating". However the main algorithmic speedup (being 5x faster than the official kernel) is undoubtedly due to the NbE algorithm.

| Kernel                                                                                | Mathlib |
| ------------------------------------------------------------------------------------- | ------- |
| **zignodamus**                                                                        | 5.9m    |
| still-nanoda ([06a07b7](https://github.com/SchrodingerZhu/still-nanoda/tree/06a07b7)) | 15.7m   |
| nanoda ([f58f2f6](https://github.com/ammkrn/nanoda_lib/tree/f58f2f6))                 | 22.6m   |
| official ([4.29.0](https://github.com/leanprover/lean4/tree/v4.29.0))                 | 32.5m   |

Time is measured in instructions, divided by 6GHz.

## Tricks used

### Algorithmic

- [Normalisation by evaluation](https://en.wikipedia.org/wiki/Normalisation_by_evaluation)
- [Glued evaluation](https://github.com/AndrasKovacs/smalltt#glued-evaluation)
- [Approximate conversion checking](https://github.com/AndrasKovacs/smalltt#approximate-conversion-checking)
- Closure capture minimisation by free variable set tracking
- Over-approximation of loose free variables (from nanoda)
- Arity-annotated values with a fast apply-n path ([eval/apply](docs/apply-n-arity.md))

### Engineering

- A ton of [interning](<https://en.wikipedia.org/wiki/Interning_(computer_science)>)
- Bit packing making use of [alignment](https://en.wikipedia.org/wiki/Data_structure_alignment) and the 16 free bits in 48-bit addresses (that do not occupy all 64 bits)
- Fast path parsing (yes I know this is basically betting on the lean4export format)
- SIMD within a register (SWAR) digit parsing
- Memory mapping
