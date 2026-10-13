import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Localization.FractionRing

#check Matrix.mul_apply
#check Matrix.det_mul
#check Matrix.det_transpose
#check Matrix.det_of_lowerTriangular
#check DyckWord.semilength
#check (fun n : ℕ => (inferInstance : Fintype {p : DyckWord // p.semilength = n}))
#check MvPolynomial.rename
#check MvPolynomial.rename_injective
#check IsFractionRing.injective
