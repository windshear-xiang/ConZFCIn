# Sources

`Vendor/ConZF/` contains the reused modules from Cameron Freer's [ConZF fork](https://github.com/cameronfreer/ConZF/tree/13ce7248321dd8b19deb73122dceb962177c73ad), fixed at commit `13ce7248321dd8b19deb73122dceb962177c73ad` on the `no-em-bounds` branch.

The original project is Mario Carneiro's [digama0/ConZF](https://github.com/digama0/ConZF). Freer's extension supplies the seeded models, universe lift, Hartogs and inaccessible-interval arguments, constructible class, choice proof, and single-inaccessible consistency endpoint. `Acc.lean` includes Cameron Zwarich's membership-accessibility work, introduced in [commit 66771d03](https://github.com/cameronfreer/ConZF/commit/66771d03e63f3bff62be65b89d5e105dd8f40295).

The vendored Lean files differ from the fixed source only in their import prefix: `ConZF.` becomes `Vendor.ConZF.`. Their `PSet` namespace and proof bodies are preserved.

The project's `ConZFCIn/Universe/` and `ConZFCIn/Model/` modules also adapt and generalize the fork's constructions to a common higher universe and a shared seeded class. Their source headers identify the corresponding upstream modules. The finite inaccessible formulas, chain bridges, and instance assembly are in `ConZFCIn/`.
