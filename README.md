# ConZFCIn

A proof of the consistency of ZFC with at least `n` strongly inaccessible cardinals in axiom-free Lean 4, from excluded middle alone, for each externally fixed natural number `n`.

The result is `EM → PSet.Con (ConZFCIn.ZFCIn n)`. For example:

```lean
theorem ConZFCIn.con_ZFCIn_3 (em : ∀ p : Prop, p ∨ ¬p) :
    PSet.Con (ConZFCIn.ZFCIn 3)
```

Excluded middle is the only hypothesis, not a declared axiom. The proofs use no `Classical.choice`, `propext`, or `Quot.sound`. `ZFCIn n` contains the full first-order ZF schemas, choice, and a sentence asserting a strictly increasing chain of `n` strongly inaccessible cardinals. `Con` is non-derivability of falsity in the inherited Hilbert-style proof system.

The proofs form an external scheme: for positive `n`, the universe levels run from `Type 0` through `Type (n+1)`. Each instance constructs all its witnesses in one common constructible class. The [complete proof for two inaccessibles](ConZFCIn/Instances/N2.lean) shows the scheme directly; [generate.py](generate.py) produces a complete Lean proof for any fixed `n`.

## Build

Lean 4.34.0, with no Mathlib or external package dependencies:

```sh
lake build
python generate.py 8
lake env lean ConZFCIn/Instances/N8.lean
```

The generator writes Lean source; the resulting proof is checked by Lean's kernel.

## Files

| File or directory                         | Content                                                                                           |
| ----------------------------------------- | ------------------------------------------------------------------------------------------------- |
| `ConZFCIn/Definitions.lean`               | The finite inaccessible sentence and target theory                                                |
| `ConZFCIn/Logic/FiniteInaccessibles.lean` | Formula readback, finite chains, distinctness, and consistency from a model                       |
| `ConZFCIn/Universe/`                      | Embeddings into a common higher universe, Hartogs bounds, and strictly increasing heights         |
| `ConZFCIn/Model/`                         | The common seeded constructible class, cofinality, inaccessible intervals, and soundness assembly |
| `ConZFCIn/Instances/`                     | Complete proofs for individual fixed values of `n`                                                |
| `generate.py`                             | The external proof generator                                                                      |
| `Vendor/ConZF/`                           | Reused set-theoretic and logical machinery                                                        |

The development builds on Mario Carneiro's [ConZF](https://github.com/digama0/ConZF), Cameron Freer's [extension](https://github.com/cameronfreer/ConZF/tree/13ce7248321dd8b19deb73122dceb962177c73ad), and Cameron Zwarich's membership-accessibility work. The common-model and finite-chain extension reuses and generalizes that machinery; see [source attribution](Vendor/SOURCES.md). This development and its documentation were prepared with AI assistance.
