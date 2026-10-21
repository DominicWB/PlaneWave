import PlaneWave.SamePair.ThirdGenerator

/-!
# Same-pair third order, part 8: orders of the constants and the package

* The constants of the same-pair block are `O(n⁻³ polylog n)` (in the class `PL _ (-3)` of
  `PlaneWave.Source.PowerPolylog`): `B_j` (`lem:h3`), `D` (its diagonal), `C_R3` (`lem:res3`), `C_Σ3` (the Schur bound
  of `Σ₃^sp`). With the explicit forms: `B_j, D, C_R3 = O(n⁻³ log n)`, `C_Σ3 = O(n⁻³ log⁴ n)`.
* **`same_pair_package`**: for every cutoff, `H₃^ret = H₃^sp + H₃^mp` (same-pair and
  multi-channel words), `H₃^sp = H₃^{gap,sp} + H₃^{res,sp}`, `Σ₃^sp` skew-adjoint with
  `[Σ₃^sp, A] = -(H₃^sp - H₃^{res,sp})`, `‖Σ₃^sp‖ ≤ C_Σ3(n)` and `‖H₃^{res,sp} u‖ ≤ C_R3(n) M` on
  good states: the same-pair class of the formal hypotheses of `thm:src3` (`‖Σ₃‖`, `‖H₃^res u‖`
  and the homological equation), with room to spare (`n⁻³` instead of `n⁻²` for `Σ₃`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace

namespace FSAsymp

open FSNormal PL

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ}

/-! ## Orders of the constants -/

theorem pl_inv3 (c : ℝ) : PL (fun n => c / (n : ℝ) ^ 3) (-3) :=
  (cnpow c (-3)).congr ⟨1, fun n hn => by
    rw [Real.rpow_neg (Nat.cast_nonneg n), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, div_eq_mul_inv]⟩

theorem pl_C3c (j : Ch eta) : PL (fun n => C3c sys L n j) (-3) :=
  (pl_inv3 (chbT sys L * (2 * muCh sys j / gF L ^ 2) * chC sys L j)).congr
    ⟨0, fun n _ => by unfold C3c; ring⟩

theorem pl_Asj (j : Ch eta) : PL (fun n => Asj sys L n j) (-1) :=
  (cnpow (chC sys L j / cgap sys (gF L) * (416 / 3)) (-1)).congr ⟨1, fun n hn => by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (n : ℝ) ≠ 0 := by positivity
    rw [Real.rpow_neg_one]
    unfold Asj
    field_simp⟩

theorem pl_Bh3 (heta : 0 < eta) (j : Ch eta) : PL (fun n => Bh3 sys L n j) (-3) := by
  have h1 := ((pl_C3c sys (L := L) j).const_mul 2).mul
    (((pl_Jn sys heta).add' (const 2)).const_mul FSLattice.Ch3)
  have h2 := (((lin 4).mul (pl_Asj sys (L := L) j)).mul (pl_inv3 (chb sys L j)))
  refine ((h1.mono (by norm_num : (-3 : ℝ) + max 0 0 ≤ -3)).add
    (h2.mono (by norm_num : (1 : ℝ) + -1 + -3 ≤ -3))).congr ⟨0, fun n _ => ?_⟩
  unfold Bh3
  ring

theorem pl_Dh3 (heta : 0 < eta) : PL (fun n => Dh3 sys L n) (-3) := by
  unfold Dh3
  refine PL.sum _ fun j _ => ?_
  have h1 := ((pl_C3c sys (L := L) j).const_mul 2).mul
    ((((pl_Jn sys heta).const_mul 2).add' (const 3)).const_mul 22000)
  have h2 := ((pl_Asj sys (L := L) j).const_mul 2).mul (pl_inv3 (chb sys L j))
  refine ((h1.mono (by norm_num : (-3 : ℝ) + max 0 0 ≤ -3)).add
    (h2.mono (by norm_num : (-1 : ℝ) + -3 ≤ -3))).congr ⟨0, fun n _ => ?_⟩
  ring

theorem pl_CR3 (heta : 0 < eta) : PL (fun n => CR3 sys L n) (-3) := by
  have h := (PL.sum (Finset.univ : Finset (Ch eta)) fun j _ => pl_Bh3 sys (L := L) heta j).const_mul
    (10 * (440000 / c0 L ^ 2 + 3520000))
  refine ((pl_Dh3 sys (L := L) heta).add h).congr ⟨0, fun n _ => ?_⟩
  unfold CR3
  rfl

theorem pl_CS3 (heta : 0 < eta) : PL (fun n => CS3 sys L n) (-3) := by
  unfold CS3
  refine PL.sum _ fun j _ => ?_
  have hJ1 : PL (fun n => ((Jn sys n + 1 : ℕ) : ℝ)) 0 :=
    ((pl_Jn sys heta).add' (const 1)).congr ⟨0, fun n _ => by push_cast; ring⟩ |>.mono
      (by norm_num)
  have h1 := (((pl_Bh3 sys (L := L) heta j).mul ((pl_Jn sys heta).add' (const 4))).mul_const
    (2 * muCh sys j / gF L ^ 2)).mul
    (((hJ1.const_mul 2).add' (const 3)).const_mul 11000 |>.mul (hJ1.add' (const 1)))
  refine (h1.mono (by norm_num)).congr ⟨0, fun n _ => ?_⟩
  ring

end FSAsymp

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- **The same-pair third order**: the decomposition of `H₃^ret` into its same-pair and
multi-channel components, the split of the same-pair component at the formal floor, and the
same-pair third generator with its homological equation, skewness and Schur bound, and the
resonant residual on good states (`lem:h3`, `lem:res3`, `Σ₃`, same-pair class). -/
theorem same_pair_package (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q) :
    (H3ret sys hL hn H : En eta n →ₗ[ℂ] En eta n) = H3sp sys L n + H3mp sys L n ∧
    H3sp sys L n = H3gapSp sys L n + H3resSp sys L n ∧
    (∀ u v : En eta n, ⟪Sig3sp sys L n u, v⟫_ℂ = -⟪u, Sig3sp sys L n v⟫_ℂ) ∧
    Sig3sp sys L n ∘ₗ FSKernel.dg (fun q => (Asym sys L n q : ℂ)) -
      FSKernel.dg (fun q => (Asym sys L n q : ℂ)) ∘ₗ Sig3sp sys L n =
      -(H3sp sys L n - H3resSp sys L n) ∧
    (∀ u : En eta n, ‖Sig3sp sys L n u‖ ≤ CS3 sys L n * ‖u‖) ∧
    (∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u → ‖H3resSp sys L n u‖ ≤ CR3 sys L n * M) :=
  ⟨H3ret_decomp hL hn H hKernel, H3sp_split, inner_Sig3sp hL, comm_Sig3sp' hL,
    norm_Sig3sp_le hL hn, fun _ _ hu => norm_H3resSp_good hL hn hu⟩

end FSNormal
