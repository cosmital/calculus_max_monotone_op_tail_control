import EndOfPaper.GaussianCoordinatePermutation
import EndOfPaper.GaussianProductIBP

/-!
Genuine Gaussian integration by parts at every coordinate, transferred through actual measure-preserving Gaussian coordinate permutations.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ScalarMonotone.EndOfPaper

theorem gaussian_product_coordinate_integration_by_parts {n : ℕ}
    {f d : EuclideanSpace ℝ (Fin (n+1)) → ℝ} (i : Fin (n+1))
    (hf : Measurable f) (hd : Measurable d)
    (hfd : ∀ z : EuclideanSpace ℝ (Fin (n+1)), ∀ s : ℝ,
      HasDerivAt (fun t => f (gaussianReplace z i t)) (d (gaussianReplace z i s)) s)
    (hfI : Integrable (fun z => f (gaussianProductVector (n+1) z)) (gaussianProductMeasure (n+1)))
    (hdI : Integrable (fun z => d (gaussianProductVector (n+1) z)) (gaussianProductMeasure (n+1)))
    (hxfI : Integrable (fun z => z i*f (gaussianProductVector (n+1) z)) (gaussianProductMeasure (n+1))) :
    (∫ z, z i*f (gaussianProductVector (n+1) z) ∂gaussianProductMeasure (n+1)) =
      ∫ z, d (gaussianProductVector (n+1) z) ∂gaussianProductMeasure (n+1) := by
  let e := Equiv.swap (0 : Fin (n+1)) i
  let U := gaussianPermutation e
  have hZero : e 0 = i := Equiv.swap_apply_left 0 i
  have hInv : e.symm i = 0 := by
    apply e.injective
    simp only [e.apply_symm_apply,hZero]
  have hHead (z : Fin (n+1) → ℝ) : U (gaussianProductVector (n+1) z) i = z 0 := by
    change gaussianProductVector (n+1) z (e.symm i) = z 0
    rw [hInv]
    rfl
  have hFI := (gaussian_product_integrable_permutation e f).mpr hfI
  have hDI := (gaussian_product_integrable_permutation e d).mpr hdI
  have hXI := (gaussian_product_integrable_permutation e (fun z => z i*f z)).mpr hxfI
  change Integrable (fun z => U (gaussianProductVector (n+1) z) i*f (U (gaussianProductVector (n+1) z)))
    (gaussianProductMeasure (n+1)) at hXI
  have hXI' : Integrable (fun z => z 0*f (U (gaussianProductVector (n+1) z)))
      (gaussianProductMeasure (n+1)) := by simpa only [hHead] using hXI
  have hDeriv (u : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
      HasDerivAt (fun t => f (U (gaussianCons t u))) (d (U (gaussianCons s u))) s := by
    have hPath (t : ℝ) : U (gaussianCons t u) = gaussianReplace (U (gaussianCons s u)) i t := by
      simpa only [hZero] using gaussian_permutation_cons_replace e s t u
    have hh := hfd (U (gaussianCons s u)) s
    simpa only [← hPath] using hh
  have hh := gaussian_product_first_integration_by_parts
    (hf.comp U.continuous.measurable) (hd.comp U.continuous.measurable) hDeriv hFI hDI hXI'
  have hLeft := gaussian_product_integral_permutation e (fun z => z i*f z)
  change (∫ z, U (gaussianProductVector (n+1) z) i*f (U (gaussianProductVector (n+1) z))
    ∂gaussianProductMeasure (n+1)) = _ at hLeft
  simp only [hHead] at hLeft
  have hRight := gaussian_product_integral_permutation e d
  simp only [Function.comp_apply] at hh
  rw [hLeft,hRight] at hh
  exact hh

end ScalarMonotone.EndOfPaper
end
