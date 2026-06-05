# Proofs in Lean 4

This repository contains a collection of formal mathematical proofs implemented in the [Lean 4](https://lean-lang.org/) proof assistant, utilizing [Mathlib4](https://github.com/leanprover-community/mathlib4).

## Project Overview

The goal of this project is to showcase formalizations of classic mathematical theorems. Each proof is self-contained and demonstrates different aspects of formal verification in Lean.

### Included Proofs

- **[Infinity of Primes](Proofs/InfinitePrimes.lean)**: A formalization of Euclid's theorem stating that there are infinitely many prime numbers.
- **[Pigeonhole Principle](Proofs/PigeonholePrinciple.lean)**: Two versions of the Pigeonhole Principle: one using Mathlib's built-in theorems and another "manual" proof for educational purposes.
- **[Sum Formula](Proofs/SumFormula.lean)**: A proof by induction of the formula for the sum of the first $n$ natural numbers: $\sum_{i=0}^n i = \frac{n(n+1)}{2}$.

## Getting Started

### Prerequisites

- [Lean 4](https://lean-lang.org/lean4/doc/quickstart.html) (via `elan`)
- [Lake](https://github.com/leanprover/lean4/tree/master/src/lake) (Lean's build system, included with Lean)

### Building the Project

To build the library and verify all proofs, run:

```bash
lake build
```

This will download dependencies (including Mathlib) and compile all modules in the `Proofs/` directory.

## Project Structure

- `Proofs/`: Directory containing the individual proof files.
- `Proofs.lean`: The root library file that imports all proof modules.
- `Main.lean`: The entry point for the compiled executable.
- `lakefile.toml`: Project configuration and dependencies.
- `Tactics.lean`: Helper imports for tactics and common mathematical structures.
