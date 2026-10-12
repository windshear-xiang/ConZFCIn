import ConZFCIn.Instances.N0
import ConZFCIn.Instances.N1
import ConZFCIn.Instances.N2
import ConZFCIn.Instances.N3
import ConZFCIn.Instances.N5
import ConZFCIn.Instances.N8

/-!
Entry point for the closed consistency theorems at `n = 0, 1, 2, 3, 5, 8`.
Each theorem takes only an explicit excluded-middle parameter.

The same complete proof template for any externally fixed `n` is implemented in
`generate.py`. Every generated Lean proof must be checked by the kernel.
This is an external family of finite proofs, with universe levels expanded for each `n`.
-/
