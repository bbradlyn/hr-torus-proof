import HRTorus.ZeroModes.Canonical
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The explicit zero modes: Proposition C.explicit, the "well defined" half of Lemma C.B(b) (`ZeroModes.Explicit`)

Written by Claude Opus 5.5 (an AI model), 2026-10-26. **The definitions and statements were written first
and reviewed against the paper (the statement phase). The proof phase is complete: every reviewed statement of this
module is proved (proof phase round two), no theorem of this module is `sorry`, and the proof devices are
marked as such, in their own sections.**
The paper: the HR paper, `papers/hr/appendices/C-kernel.tex` — Proposition C.`explicit` (`kz:prop:explicit`), the
membership half of Lemma C.`B`(b) (`kz:lem:B`, "the map is well defined") with Lemma C.`even` (`kz:lem:even`) for (C2),
the merge `μ` of Lemma C.`C` (`kz:lem:C`) **on the explicit functions only**, Lemma C.`B`'s translation trick for the
independence across `ε`, and the spanning sets of Theorem C.`T2`(ii)–(iii) (`kz:thm:T2`).

## The model

* **Variables.** The explicit functions `g` are functions of `x : Fin n → ℂ` (spin up) and `y : Fin m → ℂ` (spin down), in
  `u`-units, for any `τ ∈ ℍ`; the state of `F ∈ Θ_2[ε]` and `g` is
  "`F\otimes g\mapsto F(U)\,J^2(u)\,g(u),`" on `u = (x, y) : Fin (n + m) → ℂ` (`stateFun`, `U = Σ_i u_i`).
* **Numerators instead of meromorphic functions.** `g` has poles on the up–down coincidences
  (`polarSet`: `x_a − y_k ∈ Λ_u`); its values there are Mathlib's junk values. "`$J^2g$ has no poles along any divisor, so it is holomorphic.`"
  is stated as: there is a function `f` in the Osgood class equal to `F(U) J²(u) g(u)` off the polar set
  (`IsNumerator`; such an `f` is unique, the polar set having dense complement). Every property of the state — the
  boundary conditions, antisymmetry, (C1), (C2), independence — is a property of `f`.
* **The merge `μ`** is the paper's limit "`=\lim_{v\to0}v^2g\big(w+\tfrac v2,x';w-\tfrac v2,y'\big)`" (`HasMerge`), with
  the first up and the first down variable merged, at generic points (`MergeGeneric`).
* **The additive constant of `℘`.** Mathlib's `℘` (`wp`) differs from the paper's `−(log ϑ₁)''` by a constant `c`; the
  statements below are insensitive to it, and this is where that is used: `g_{2m+1} = det[℘(x_a − y_k) | 1]` is
  unchanged by `℘ ↦ ℘ + c` (subtract `c` times the column of ones), and so is `f_5^{(p)}` (the sum of all cofactors of
  `M` is, up to sign, the determinant of `M` bordered by ones, unchanged by `M ↦ M + c𝟙𝟙ᵀ`); `d^{(p)}_ε` for `ε ≠ (1,1)`
  is built from differences `℘^{(ε)}(u) − ℘^{(ε)}(u − λ_ε)`, which do not see `c`; and `d^{(p)}_{(1,1)}` changes by
  `c f_5^{(p)}`, so the span of `{d^{(p)}_{(1,1)}, f_5^{(p)}}` — hence the span of the ten even-`N` states — is the same.
  Each property stated here (membership, (C1), (C2), the merges, the independence) holds for any `℘` satisfying
  Lemma C.theta(d) in Mathlib's form.
-/

open Complex Filter Topology
open scoped Real UpperHalfPlane Matrix

noncomputable section

namespace HRTorus.ZeroModes

/-! ## The states `F(U) J²(u) g(u)` and their numerators -/

/-- **Lemma C.B(b)**: "`F\otimes g\mapsto F(U)\,J^2(u)\,g(u),`" — the raw product, on `u = (x, y)`, `U = Σ_i u_i`. -/
def stateFun (τ : ℂ) {n m : ℕ} (F : ℂ → ℂ) (g : (Fin n → ℂ) → (Fin m → ℂ) → ℂ) (u : Fin (n + m) → ℂ) : ℂ :=
  F (∑ i, u i) * Jfun τ u ^ 2 * g (fun a => u (Fin.castAdd m a)) (fun k => u (Fin.natAdd n k))

/-- The up–down coincidence divisors `{x_a − y_k ∈ Λ_u}`, where the explicit `g` have their poles. -/
def polarSet (τ : ℍ) (n m : ℕ) : Set (Fin (n + m) → ℂ) :=
  {u | ∃ (a : Fin n) (k : Fin m), u (Fin.castAdd m a) - u (Fin.natAdd n k) ∈ Λu τ}

/-- `f` is the numerator of the state `F(U) J² g`: in the Osgood class and equal to `F(U) J²(u) g(u)` off the polar set
("`$J^2g$ has no poles along any divisor, so it is holomorphic.`"). -/
def IsNumerator (τ : ℍ) (n m : ℕ) (F : ℂ → ℂ) (g : (Fin n → ℂ) → (Fin m → ℂ) → ℂ)
    (f : (Fin (n + m) → ℂ) → ℂ) : Prop :=
  IsOsgood f ∧ ∀ u, u ∉ polarSet τ n m → f u = stateFun τ F g u

/-! ## The explicit functions of Proposition C.explicit -/

/-- **Proposition C.explicit(a)**: "`$g_{2m+1}:=\det\big[\wp(x_a-y_k)\ \big|\ 1\big]$ is the $(m+1)\times(m+1)$ determinant with entries $\wp(x_a-y_k)$, $k\le m$, and a last column of ones.`" -/
def gOdd (τ : ℍ) (m : ℕ) (x : Fin (m + 1) → ℂ) (y : Fin m → ℂ) : ℂ :=
  (Matrix.of fun (a k : Fin (m + 1)) => if h : (k : ℕ) < m then wp τ (x a - y ⟨k, h⟩) else 1).det

/-- **Theorem C.T2(ii)**: "`$S_z=-\tfrac12$ is the same with the species exchanged.`" — `g_{2m+1}` for `m` up and `m + 1`
down electrons. -/
def gOddSwap (τ : ℍ) (m : ℕ) (x : Fin m → ℂ) (y : Fin (m + 1) → ℂ) : ℂ := gOdd τ m y x

/-- **Proposition C.explicit(b)**: "`For $\varepsilon\in\{\pm1\}^2$: $d^{(p)}_\varepsilon:=\det[\wp_\varepsilon(x_i-y_j)]_{p\times p}$ lies in $\kzG(p,p;\varepsilon)$, with $\mu(d^{(p)}_\varepsilon)=d^{(p-1)}_\varepsilon$ and $\mu^{p-1}(d^{(p)}_\varepsilon)=\wp_\varepsilon$.`" -/
def dEps (τ : ℍ) (ε : Eps) (p : ℕ) (x y : Fin p → ℂ) : ℂ :=
  (Matrix.of fun (i j : Fin p) => wpE τ ε (x i - y j)).det

/-- **Proposition C.explicit(c)**: "`$f_5^{(p)}:=\sum_{i,j}(-1)^{i+j}\det M^{(ij)}$, where $M=[\wp(x_i-y_j)]$ and $M^{(ij)}$ is $M$ with row $i$ and column $j$ deleted ($f_5^{(1)}:=1$)`"
— at `p = q + 1` (for `q = 0` the sum is the one empty minor, `1`). -/
def f5 (τ : ℍ) (q : ℕ) (x y : Fin (q + 1) → ℂ) : ℂ :=
  ∑ i : Fin (q + 1), ∑ j : Fin (q + 1), (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) *
    ((Matrix.of fun (i' j' : Fin (q + 1)) => wp τ (x i' - y j')).submatrix i.succAbove j.succAbove).det

/-- The five relative states of the even case at `p = q + 1`: `d^{(p)}_ε` for `ε ∈ {±1}²` (`some ε`) and `f_5^{(p)}`
(`none`). -/
def gEven (τ : ℍ) (q : ℕ) : Option Eps → (Fin (q + 1) → ℂ) → (Fin (q + 1) → ℂ) → ℂ
  | some ε => dEps τ ε (q + 1)
  | none => f5 τ q

/-- The multiplier pair of each relative state: `ε` for `d_ε`, `(1,1)` for `f_5`. -/
def epsOf (e : Option Eps) : Eps := e.getD .pp

/-! ### Proof devices for conditions (i)–(iii) (proof phase, round two; not statements of the paper)

A determinant whose entries in one row (column) all acquire a common factor `r` is multiplied by `r`
(`det_updateRow_smul`, `det_updateCol_smul`); permuting the rows or the columns multiplies it by the sign of the
permutation (`det_permute`, `det_permute'`). `f_5^{(p)}` is the sum of the determinants of `M` with one column replaced
by ones (`f5_eq_sum_dev`, from Mathlib's `adjugate_fin_succ_eq_det_submatrix` and Cramer's rule `cramer_apply`), which
gives its antisymmetry from that of determinants. -/

theorem e1_mul_self_dev (ε : Eps) : ε.e1 * ε.e1 = 1 := by
  cases ε <;> norm_num [Eps.e1]

theorem e2_mul_self_dev (ε : Eps) : ε.e2 * ε.e2 = 1 := by
  cases ε <;> norm_num [Eps.e2]

theorem wpE_sub_one_dev (τ : ℍ) (ε : Eps) (u : ℂ) : wpE τ ε (u - 1) = ε.e1 * wpE τ ε u := by
  have h := wpE_add_one τ ε (u - 1)
  rw [sub_add_cancel] at h
  rw [h, ← mul_assoc, e1_mul_self_dev, one_mul]

theorem wpE_sub_tau_dev (τ : ℍ) (ε : Eps) (u : ℂ) : wpE τ ε (u - τ) = ε.e2 * wpE τ ε u := by
  have h := wpE_add_tau τ ε (u - τ)
  rw [sub_add_cancel] at h
  rw [h, ← mul_assoc, e2_mul_self_dev, one_mul]

theorem wp_sub_one_dev (τ : ℍ) (u : ℂ) : wp τ (u - 1) = wp τ u := by
  have h := wp_add_one τ (u - 1)
  rw [sub_add_cancel] at h
  exact h.symm

theorem wp_sub_tau_dev (τ : ℍ) (u : ℂ) : wp τ (u - τ) = wp τ u := by
  have h := wp_add_tau τ (u - τ)
  rw [sub_add_cancel] at h
  exact h.symm

/-- A common factor of the entries of row `a`. -/
theorem det_row_mul_dev {n : ℕ} (E : ℂ → Fin n → ℂ) (x : Fin n → ℂ) (a : Fin n) (c r : ℂ)
    (h : ∀ j, E (x a + c) j = r * E (x a) j) :
    (Matrix.of fun i j => E (Function.update x a (x a + c) i) j).det = r * (Matrix.of fun i j => E (x i) j).det := by
  have e : (Matrix.of fun i j => E (Function.update x a (x a + c) i) j) =
      Matrix.updateRow (Matrix.of fun i j => E (x i) j) a (r • (Matrix.of fun i j => E (x i) j) a) := by
    ext i j
    by_cases hi : i = a
    · subst hi
      simp [h]
    · simp [hi]
  rw [e, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]

/-- A common factor of the entries of column `k`. -/
theorem det_col_mul_dev {n : ℕ} (E : Fin n → ℂ → ℂ) (y : Fin n → ℂ) (k : Fin n) (c r : ℂ)
    (h : ∀ i, E i (y k + c) = r * E i (y k)) :
    (Matrix.of fun i j => E i (Function.update y k (y k + c) j)).det = r * (Matrix.of fun i j => E i (y j)).det := by
  have e : (Matrix.of fun i j => E i (Function.update y k (y k + c) j)) =
      Matrix.updateCol (Matrix.of fun i j => E i (y j)) k (r • fun i => (Matrix.of fun i j => E i (y j)) i k) := by
    ext i j
    by_cases hj : j = k
    · subst hj
      simp [h]
    · simp [hj]
  rw [e, Matrix.det_updateCol_smul, Matrix.updateCol_eq_self]

/-- A transposition of the rows. -/
theorem det_rows_swap_dev {n : ℕ} (E : ℂ → Fin n → ℂ) (x : Fin n → ℂ) {a b : Fin n} (hab : a ≠ b) :
    (Matrix.of fun i j => E ((x ∘ Equiv.swap a b) i) j).det = -(Matrix.of fun i j => E (x i) j).det := by
  have e : (Matrix.of fun i j => E ((x ∘ Equiv.swap a b) i) j) =
      (Matrix.of fun i j => E (x i) j).submatrix (Equiv.swap a b) id := by
    ext i j
    rfl
  rw [e, Matrix.det_permute, Equiv.Perm.sign_swap hab]
  push_cast
  ring

/-- A transposition of the columns. -/
theorem det_cols_swap_dev {n : ℕ} (E : Fin n → ℂ → ℂ) (y : Fin n → ℂ) {k l : Fin n} (hkl : k ≠ l) :
    (Matrix.of fun i j => E i ((y ∘ Equiv.swap k l) j)).det = -(Matrix.of fun i j => E i (y j)).det := by
  have e : (Matrix.of fun i j => E i ((y ∘ Equiv.swap k l) j)) =
      (Matrix.of fun i j => E i (y j)).submatrix id (Equiv.swap k l) := by
    ext i j
    rfl
  rw [e, Matrix.det_permute', Equiv.Perm.sign_swap hkl]
  push_cast
  ring

/-- The matrix of `g_{2m+1}` after a transposition of the `y`'s: a transposition of its first `m` columns. -/
theorem gOdd_matrix_swap_y_dev (τ : ℍ) (m : ℕ) (x : Fin (m + 1) → ℂ) (y : Fin m → ℂ) (k l : Fin m) :
    (Matrix.of fun (a c : Fin (m + 1)) => if h : (c : ℕ) < m then wp τ (x a - (y ∘ Equiv.swap k l) ⟨c, h⟩) else 1) =
      (Matrix.of fun (a c : Fin (m + 1)) => if h : (c : ℕ) < m then wp τ (x a - y ⟨c, h⟩) else 1).submatrix id
        (Equiv.swap (Fin.castSucc k) (Fin.castSucc l)) := by
  ext a c
  simp only [Matrix.of_apply, Matrix.submatrix_apply, id, Function.comp_apply]
  refine Fin.lastCases ?_ (fun c' => ?_) c
  · have h1 : Equiv.swap (Fin.castSucc k) (Fin.castSucc l) (Fin.last m) = Fin.last m :=
      Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_lt_last k).ne' (Fin.castSucc_lt_last l).ne'
    rw [h1]
    simp
  · rw [(Fin.castSucc_injective m).swap_apply]
    simp

/-- `f_5^{(p)} = Σ_j det(M with column j replaced by ones)`. -/
theorem f5_eq_sum_dev (τ : ℍ) (q : ℕ) (x y : Fin (q + 1) → ℂ) :
    f5 τ q x y = ∑ j, ((Matrix.of fun (i' j' : Fin (q + 1)) => wp τ (x i' - y j')).updateCol j fun _ => 1).det := by
  set M := Matrix.of fun (i' j' : Fin (q + 1)) => wp τ (x i' - y j') with hM
  have h1 : f5 τ q x y = ∑ i, ∑ j, M.adjugate j i := by
    unfold f5
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp [Matrix.mulVec, dotProduct]

/-! ## Conditions (i)–(iii) of Definition C.G for the explicit functions

Definition C.G's "`$g(u+c\one)=g(u)$ for all $c\in\C$`", "`$g(u+e_k)=\varepsilon_1g(u)$ and $g(u+\tau e_k)=\varepsilon_2g(u)$ for every $k$`"
and "`$g$ is antisymmetric in the $x$'s and in the $y$'s`", for the explicit `g` (identities of functions; at the poles
both sides carry Mathlib's junk values, and the identities hold there too). Conditions (iv)–(v) enter only through the
numerators: `IsNumerator` and the (C2) statements below. -/

/-- **Proposition C.explicit(b)**, membership (i)–(iii): "`(i): entries depend on differences.`"
"`(ii): each entry $\wp_\varepsilon(x_i-y_j)$ has multiplier $\varepsilon_1$ under $x_i\mapsto x_i+1$ and $\varepsilon_1^{-1}=\varepsilon_1$ under $y_j\mapsto y_j+1$.`"
"`(iii): rows and columns.`" -/
theorem dEps_G (τ : ℍ) (ε : Eps) (p : ℕ) :
    (∀ (x y : Fin p → ℂ) (c : ℂ), dEps τ ε p (fun i => x i + c) (fun j => y j + c) = dEps τ ε p x y) ∧
    (∀ (x y : Fin p → ℂ) (a : Fin p), dEps τ ε p (Function.update x a (x a + 1)) y = ε.e1 * dEps τ ε p x y) ∧
    (∀ (x y : Fin p → ℂ) (a : Fin p), dEps τ ε p (Function.update x a (x a + τ)) y = ε.e2 * dEps τ ε p x y) ∧
    (∀ (x y : Fin p → ℂ) (k : Fin p), dEps τ ε p x (Function.update y k (y k + 1)) = ε.e1 * dEps τ ε p x y) ∧
    (∀ (x y : Fin p → ℂ) (k : Fin p), dEps τ ε p x (Function.update y k (y k + τ)) = ε.e2 * dEps τ ε p x y) ∧
    (∀ (x y : Fin p → ℂ) (a b : Fin p), a ≠ b → dEps τ ε p (x ∘ Equiv.swap a b) y = -dEps τ ε p x y) ∧
    (∀ (x y : Fin p → ℂ) (k l : Fin p), k ≠ l → dEps τ ε p x (y ∘ Equiv.swap k l) = -dEps τ ε p x y) := by
  refine ⟨fun x y c => ?_, fun x y a => ?_, fun x y a => ?_, fun x y k => ?_, fun x y k => ?_,
    fun x y a b hab => ?_, fun x y k l hkl => ?_⟩
  · unfold dEps
    congr 1
    ext i j
    simp only [Matrix.of_apply, add_sub_add_right_eq_sub]
  · exact det_row_mul_dev (fun w j => wpE τ ε (w - y j)) x a 1 ε.e1 fun j => by
      show wpE τ ε (x a + 1 - y j) = ε.e1 * wpE τ ε (x a - y j)
      rw [show x a + 1 - y j = (x a - y j) + 1 by ring, wpE_add_one]
  · exact det_row_mul_dev (fun w j => wpE τ ε (w - y j)) x a τ ε.e2 fun j => by
      show wpE τ ε (x a + τ - y j) = ε.e2 * wpE τ ε (x a - y j)
      rw [show x a + (τ : ℂ) - y j = (x a - y j) + τ by ring, wpE_add_tau]
  · exact det_col_mul_dev (fun i w => wpE τ ε (x i - w)) y k 1 ε.e1 fun i => by
      show wpE τ ε (x i - (y k + 1)) = ε.e1 * wpE τ ε (x i - y k)
      rw [show x i - (y k + 1) = (x i - y k) - 1 by ring, wpE_sub_one_dev]
  · exact det_col_mul_dev (fun i w => wpE τ ε (x i - w)) y k τ ε.e2 fun i => by
      show wpE τ ε (x i - (y k + τ)) = ε.e2 * wpE τ ε (x i - y k)
      rw [show x i - (y k + (τ : ℂ)) = (x i - y k) - τ by ring, wpE_sub_tau_dev]
  · exact det_rows_swap_dev (fun w j => wpE τ ε (w - y j)) x hab
  · exact det_cols_swap_dev (fun i w => wpE τ ε (x i - w)) y hkl

/-- **Proposition C.explicit(a)**, membership (i)–(iii) with `ε = (1,1)` ("`in (a) the terms with a $1$ in row $a$ are free of $x_a$, which is consistent because $\varepsilon=(1,1)$ there.`"). -/
theorem gOdd_G (τ : ℍ) (m : ℕ) :
    (∀ (x : Fin (m + 1) → ℂ) (y : Fin m → ℂ) (c : ℂ), gOdd τ m (fun i => x i + c) (fun j => y j + c) = gOdd τ m x y) ∧
    (∀ (x : Fin (m + 1) → ℂ) (y : Fin m → ℂ) (a : Fin (m + 1)),
      gOdd τ m (Function.update x a (x a + 1)) y = gOdd τ m x y ∧
        gOdd τ m (Function.update x a (x a + τ)) y = gOdd τ m x y) ∧
    (∀ (x : Fin (m + 1) → ℂ) (y : Fin m → ℂ) (k : Fin m),
      gOdd τ m x (Function.update y k (y k + 1)) = gOdd τ m x y ∧
        gOdd τ m x (Function.update y k (y k + τ)) = gOdd τ m x y) ∧
    (∀ (x : Fin (m + 1) → ℂ) (y : Fin m → ℂ) (a b : Fin (m + 1)), a ≠ b →
      gOdd τ m (x ∘ Equiv.swap a b) y = -gOdd τ m x y) ∧
    (∀ (x : Fin (m + 1) → ℂ) (y : Fin m → ℂ) (k l : Fin m), k ≠ l →
      gOdd τ m x (y ∘ Equiv.swap k l) = -gOdd τ m x y) := by
  have hcongr : ∀ (x x' : Fin (m + 1) → ℂ) (y y' : Fin m → ℂ),
      (∀ a k, wp τ (x a - y k) = wp τ (x' a - y' k)) → gOdd τ m x y = gOdd τ m x' y' := by
    intro x x' y y' h
    unfold gOdd
    congr 1
    ext a c
    simp only [Matrix.of_apply]
    split_ifs with hc
    · exact h a _
    · rfl
  refine ⟨fun x y c => ?_, fun x y a => ⟨?_, ?_⟩, fun x y k => ⟨?_, ?_⟩, fun x y a b hab => ?_,
    fun x y k l hkl => ?_⟩
  · exact hcongr _ _ _ _ fun a k => by rw [add_sub_add_right_eq_sub]
  · refine hcongr _ _ _ _ fun b k => ?_
    by_cases hb : b = a
    · subst hb
      rw [Function.update_self, show x b + 1 - y k = (x b - y k) + 1 by ring, wp_add_one]
    · rw [Function.update_of_ne hb]
  · refine hcongr _ _ _ _ fun b k => ?_
    by_cases hb : b = a
    · subst hb
      rw [Function.update_self, show x b + (τ : ℂ) - y k = (x b - y k) + τ by ring, wp_add_tau]
    · rw [Function.update_of_ne hb]
  · refine hcongr _ _ _ _ fun a l => ?_
    by_cases hl : l = k
    · subst hl
      rw [Function.update_self, show x a - (y l + 1) = (x a - y l) - 1 by ring, wp_sub_one_dev]
    · rw [Function.update_of_ne hl]
  · refine hcongr _ _ _ _ fun a l => ?_
    by_cases hl : l = k
    · subst hl
      rw [Function.update_self, show x a - (y l + (τ : ℂ)) = (x a - y l) - τ by ring, wp_sub_tau_dev]
    · rw [Function.update_of_ne hl]
  · unfold gOdd
    exact det_rows_swap_dev (fun w (c : Fin (m + 1)) => if h : (c : ℕ) < m then wp τ (w - y ⟨c, h⟩) else 1) x hab
  · unfold gOdd
    rw [gOdd_matrix_swap_y_dev, Matrix.det_permute', Equiv.Perm.sign_swap ((Fin.castSucc_injective m).ne hkl)]
    push_cast
    ring

/-- **Proposition C.explicit(c)**, membership (i)–(iii) with `ε = (1,1)`. -/
theorem f5_G (τ : ℍ) (q : ℕ) :
    (∀ (x y : Fin (q + 1) → ℂ) (c : ℂ), f5 τ q (fun i => x i + c) (fun j => y j + c) = f5 τ q x y) ∧
    (∀ (x y : Fin (q + 1) → ℂ) (a : Fin (q + 1)),
      f5 τ q (Function.update x a (x a + 1)) y = f5 τ q x y ∧ f5 τ q (Function.update x a (x a + τ)) y = f5 τ q x y) ∧
    (∀ (x y : Fin (q + 1) → ℂ) (k : Fin (q + 1)),
      f5 τ q x (Function.update y k (y k + 1)) = f5 τ q x y ∧ f5 τ q x (Function.update y k (y k + τ)) = f5 τ q x y) ∧
    (∀ (x y : Fin (q + 1) → ℂ) (a b : Fin (q + 1)), a ≠ b → f5 τ q (x ∘ Equiv.swap a b) y = -f5 τ q x y) ∧
    (∀ (x y : Fin (q + 1) → ℂ) (k l : Fin (q + 1)), k ≠ l → f5 τ q x (y ∘ Equiv.swap k l) = -f5 τ q x y) := by
  have hcongr : ∀ x x' y y' : Fin (q + 1) → ℂ,
      (∀ i j, wp τ (x i - y j) = wp τ (x' i - y' j)) → f5 τ q x y = f5 τ q x' y' := by
    intro x x' y y' h
    have hM : (Matrix.of fun (i j : Fin (q + 1)) => wp τ (x i - y j)) = Matrix.of fun i j => wp τ (x' i - y' j) := by
      ext i j
      exact h i j
    unfold f5
    rw [hM]
  refine ⟨fun x y c => ?_, fun x y a => ⟨?_, ?_⟩, fun x y k => ⟨?_, ?_⟩, fun x y a b hab => ?_,
    fun x y k l hkl => ?_⟩
  · exact hcongr _ _ _ _ fun i j => by rw [add_sub_add_right_eq_sub]
  · refine hcongr _ _ _ _ fun b k => ?_
    by_cases hb : b = a
    · subst hb
      rw [Function.update_self, show x b + 1 - y k = (x b - y k) + 1 by ring, wp_add_one]
    · rw [Function.update_of_ne hb]
  · refine hcongr _ _ _ _ fun b k => ?_
    by_cases hb : b = a
    · subst hb
      rw [Function.update_self, show x b + (τ : ℂ) - y k = (x b - y k) + τ by ring, wp_add_tau]
    · rw [Function.update_of_ne hb]
  · refine hcongr _ _ _ _ fun a l => ?_
    by_cases hl : l = k
    · subst hl
      rw [Function.update_self, show x a - (y l + 1) = (x a - y l) - 1 by ring, wp_sub_one_dev]
    · rw [Function.update_of_ne hl]
  · refine hcongr _ _ _ _ fun a l => ?_
    by_cases hl : l = k
    · subst hl
      rw [Function.update_self, show x a - (y l + (τ : ℂ)) = (x a - y l) - τ by ring, wp_sub_tau_dev]
    · rw [Function.update_of_ne hl]
  · rw [f5_eq_sum_dev, f5_eq_sum_dev, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : ((Matrix.of fun (i' j' : Fin (q + 1)) => wp τ ((x ∘ Equiv.swap a b) i' - y j')).updateCol j
        fun _ => 1) = ((Matrix.of fun (i' j' : Fin (q + 1)) => wp τ (x i' - y j')).updateCol j
          fun _ => 1).submatrix (Equiv.swap a b) id := by
      ext i c
      simp [Matrix.updateCol_apply]
    rw [e, Matrix.det_permute, Equiv.Perm.sign_swap hab]
    push_cast
    ring
  · rw [f5_eq_sum_dev, f5_eq_sum_dev, ← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.swap k l) _ _ fun j => ?_
    have e : ((Matrix.of fun (i' j' : Fin (q + 1)) => wp τ (x i' - (y ∘ Equiv.swap k l) j')).updateCol j
        fun _ => 1) = ((Matrix.of fun (i' j' : Fin (q + 1)) => wp τ (x i' - y j')).updateCol (Equiv.swap k l j)
          fun _ => 1).submatrix id (Equiv.swap k l) := by
      ext i c
      by_cases hc : c = j
      · subst hc
        simp
      · simp [hc, (Equiv.swap k l).injective.ne hc]
    rw [e, Matrix.det_permute', Equiv.Perm.sign_swap hkl]
    push_cast
    ring

/-! ### Proof devices for Lemma C.even and for `D_{st} = 2∂_v` (proof phase, round two; not statements of the paper)

The derivative at `0` of an even function vanishes (`deriv_even_zero_dev`, from `deriv_comp_neg`). The Osgood class on
`ℂ × ℂ` and its Fréchet differentiability are the stage-F scouting pilot's (its `Osgood.lean`,
outside this repository: `IsOsgood2`, `D1`, `D1int`, `D1int_continuous`, `D1_eq_integral`, `D1_continuous`,
`isOsgood2_swap`, `isOsgood2_differentiable`), copied verbatim but for the suffix `_dev` on every name: both partial
derivatives are continuous by Cauchy's formula, and Mathlib's `hasStrictFDerivAt_uncurry_coprod` gives the
differentiability, hence the chain rule along `(u_s, u_t) = (R + v/2, R − v/2)`. -/

theorem deriv_even_zero_dev {P : ℂ → ℂ} (hP : ∀ v, P (-v) = P v) : deriv P 0 = 0 := by
  have h := deriv_comp_neg (f := P) (x := 0)
  have hfun : (fun x => P (-x)) = P := funext hP
  rw [hfun, neg_zero] at h
  linear_combination h / 2

section OsgoodDevices

open Set MeasureTheory


/-- The Osgood class on `ℂ × ℂ`: continuous, and entire in each variable separately. -/
structure IsOsgood2_dev (a : ℂ × ℂ → ℂ) : Prop where
  cont : Continuous a
  fst : ∀ y, Differentiable ℂ (fun x => a (x, y))
  snd : ∀ x, Differentiable ℂ (fun y => a (x, y))
variable {a : ℂ × ℂ → ℂ}


/-- `∂₁a`, the derivative in the first variable at fixed second variable. -/
def D1_dev (a : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ := deriv (fun x => a (x, p.2)) p.1

/-- The integrand of Cauchy's formula for `∂₁a` on the unit circle about `p.1`. -/
def D1int_dev (a : ℂ × ℂ → ℂ) (p : ℂ × ℂ) (θ : ℝ) : ℂ :=
  (circleMap 0 1 θ * I) * ((1 / (circleMap 0 1 θ) ^ 2) * a (p.1 + circleMap 0 1 θ, p.2))

theorem D1int_continuous_dev (ha : IsOsgood2_dev a) : Continuous (Function.uncurry (D1int_dev a)) := by
  have hc : Continuous fun θ : ℝ => circleMap 0 1 θ := continuous_circleMap 0 1
  have hne : ∀ θ : ℝ, circleMap 0 1 θ ^ 2 ≠ 0 := fun θ => pow_ne_zero 2 (circleMap_ne_center one_ne_zero)
  have hinv : Continuous fun θ : ℝ => 1 / circleMap 0 1 θ ^ 2 :=
    continuous_const.div (hc.pow 2) hne
  have ha' : Continuous fun q : (ℂ × ℂ) × ℝ => a (q.1.1 + circleMap 0 1 q.2, q.1.2) :=
    ha.cont.comp ((continuous_fst.fst.add (hc.comp continuous_snd)).prodMk continuous_fst.snd)
  exact ((hc.comp continuous_snd).mul continuous_const).mul ((hinv.comp continuous_snd).mul ha')

/-- Cauchy's formula: `2πi · ∂₁a(p) = ∫_0^{2π} (integrand) dθ`. -/
theorem D1_eq_integral_dev (ha : IsOsgood2_dev a) (p : ℂ × ℂ) :
    (2 * π * I) * D1_dev a p = ∫ θ in (0 : ℝ)..2 * π, D1int_dev a p θ := by
  have h := (ha.fst p.2).differentiableOn.deriv_eq_smul_circleIntegral (c := p.1) one_pos
  unfold circleIntegral at h
  unfold D1_dev
  rw [← smul_eq_mul, ← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [D1int_dev, smul_eq_mul, deriv_circleMap, circleMap_sub_center]
  congr 3
  simp [circleMap]

theorem D1_continuous_dev (ha : IsOsgood2_dev a) : Continuous (D1_dev a) := by
  have hI : Continuous fun p : ℂ × ℂ => ∫ θ in (0 : ℝ)..2 * π, D1int_dev a p θ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (D1int_continuous_dev ha) _ _
  have e : D1_dev a = fun p => (2 * π * I)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, D1int_dev a p θ := by
    funext p
    rw [← D1_eq_integral_dev ha p, ← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_mul]
  rw [e]
  exact continuous_const.mul hI


theorem isOsgood2_swap_dev (ha : IsOsgood2_dev a) : IsOsgood2_dev (fun p : ℂ × ℂ => a (p.2, p.1)) :=
  ⟨ha.cont.comp continuous_swap, fun y => ha.snd y, fun x => ha.fst x⟩

theorem isOsgood2_differentiable_dev (ha : IsOsgood2_dev a) : Differentiable ℂ a := by
  intro u
  have hD1 := D1_continuous_dev ha
  have hD2 : Continuous fun p : ℂ × ℂ => D1_dev (fun p : ℂ × ℂ => a (p.2, p.1)) (p.2, p.1) :=
    (D1_continuous_dev (isOsgood2_swap_dev ha)).comp continuous_swap
  have hs := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℂ) (u := u) (f := fun x y => a (x, y))
    (f₁ := fun x y => ContinuousLinearMap.toSpanSingleton ℂ (D1_dev a (x, y)))
    (f₂ := fun x y => ContinuousLinearMap.toSpanSingleton ℂ
      (D1_dev (fun p : ℂ × ℂ => a (p.2, p.1)) (y, x)))
    (Filter.Eventually.of_forall fun v => ((ha.fst v.2) v.1).hasDerivAt.hasFDerivAt)
    (Filter.Eventually.of_forall fun v => ((ha.snd v.1) v.2).hasDerivAt.hasFDerivAt)
    (((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℂ) (E := ℂ)).continuous.comp hD1).continuousAt)
    (((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℂ) (E := ℂ)).continuous.comp hD2).continuousAt)
  exact hs.hasFDerivAt.differentiableAt


end OsgoodDevices

/-! ## Lemma C.even -/

/-- **Lemma C.even**: "`Then $[\kzD_{x_ay_k}\mathsf a]_{x_a=y_k}\equiv0$ iff $\mathcal B\equiv0$.`" — at fixed pair centre
and fixed other variables, in the relative coordinate `v`: for `S` analytic and even at `0` and
`g = 𝒜v⁻² + ℬv⁻¹ + O(1)`, the product `S ϑ₁(v)² g` extends analytically to `0`, with derivative `S(0) ϑ₁'(0)² ℬ` there
(the proof: "`$[\kzD\mathsf a]_{v=0}=2[v^1](S\kzvth_1^2g)=2e_2\mathcal B$`"). -/
theorem lemEven (τ : ℍ) {S g : ℂ → ℂ} {A B : ℂ} (hS : AnalyticAt ℂ S 0) (hSe : ∀ v, S (-v) = S v)
    (hg : AnalyticAt ℂ (fun v => g v - A / v ^ 2 - B / v) 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ (∀ᶠ v in 𝓝[≠] (0 : ℂ), h v = S v * theta1 v τ ^ 2 * g v) ∧
      deriv h 0 = S 0 * deriv (fun v => theta1 v τ) 0 ^ 2 * B := by
  -- `ϑ₁(v) = v φ(v)` with `φ` entire and even, `φ(0) = ϑ₁'(0)`; `g = A v⁻² + B v⁻¹ + R` with `R` analytic at `0`
  set θ : ℂ → ℂ := fun v => theta1 v τ with hθ
  have hθd : Differentiable ℂ θ := theta1_differentiable τ
  set φ : ℂ → ℂ := dslope θ 0 with hφ
  have hφd : Differentiable ℂ φ := by
    have h := (differentiableOn_dslope (s := Set.univ) (c := (0 : ℂ)) Filter.univ_mem).2 hθd.differentiableOn
    exact fun z => (h z (Set.mem_univ z)).differentiableAt Filter.univ_mem
  have hθ0 : θ 0 = 0 := ThetaDev.theta1_zero τ
  have hθφ : ∀ v, θ v = v * φ v := by
    intro v
    have h := sub_smul_dslope θ 0 v
    rw [hθ0, sub_zero, sub_zero, smul_eq_mul] at h
    exact h.symm
  have hφ0 : φ 0 = deriv θ 0 := dslope_same θ 0
  have hφe : ∀ v, φ (-v) = φ v := by
    intro v
    by_cases hv : v = 0
    · rw [hv, neg_zero]
    · have h1 := hθφ (-v)
      have h2 := hθφ v
      have hodd : θ (-v) = -θ v := theta1_neg v τ
      rw [hodd, h2] at h1
      exact mul_left_cancel₀ (neg_ne_zero.2 hv) (by rw [← h1]; ring)
  set R : ℂ → ℂ := fun v => g v - A / v ^ 2 - B / v with hR
  refine ⟨fun v => S v * φ v ^ 2 * (A + B * v + v ^ 2 * R v), ?_, ?_, ?_⟩
  · exact (hS.mul ((hφd.analyticAt 0).pow 2)).mul
      ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).add ((analyticAt_id.pow 2).mul hg))
  · filter_upwards [self_mem_nhdsWithin] with v hv
    have hv' : v ≠ 0 := hv
    have e := hθφ v
    simp only [hθ] at e
    rw [e]
    simp only [hR]
    field_simp
    ring
  · have h0 : deriv (fun v => S v * φ v ^ 2) 0 = 0 :=
      deriv_even_zero_dev fun v => show S (-v) * φ (-v) ^ 2 = S v * φ v ^ 2 by rw [hSe, hφe]
    have hP : HasDerivAt (fun v => S v * φ v ^ 2) 0 0 := by
      have hPd : DifferentiableAt ℂ (fun v => S v * φ v ^ 2) 0 := hS.differentiableAt.mul ((hφd 0).pow 2)
      exact hPd.hasDerivAt.congr_deriv h0
    have hQ1 : HasDerivAt (fun v : ℂ => A + B * v) B 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul B).const_add A
    have hQ2 : HasDerivAt (fun v : ℂ => v ^ 2 * R v) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℂ)).fun_mul hg.differentiableAt.hasDerivAt
    have hQ : HasDerivAt (fun v : ℂ => A + B * v + v ^ 2 * R v) B 0 := by
      simpa using hQ1.fun_add hQ2
    rw [(hP.fun_mul hQ).deriv, hφ0]
    ring

/-- The proof of Lemma C.even: "`Since $\kzD_{x_ay_k}=2\partial_v$ at fixed $R$,`" — for `f` in the Osgood class and
`u_s = u_t = R`, `(D_{st} f)(u) = 2 ∂_v f(… R + v/2 …, … R − v/2 …)|_{v=0}`. -/
theorem relDeriv_eq_two_deriv {N : ℕ} {f : (Fin N → ℂ) → ℂ} (hf : IsOsgood f) {s t : Fin N} (hst : s ≠ t)
    (u : Fin N → ℂ) (hu : u s = u t) :
    relDeriv f s t u =
      2 * deriv (fun v => f (Function.update (Function.update u s (u s + v / 2)) t (u t - v / 2))) 0 := by
  -- the function of `(u_s, u_t)` is in F0's Osgood class on `ℂ × ℂ`, hence Fréchet differentiable: the chain rule
  set G : ℂ × ℂ → ℂ := fun p => f (Function.update (Function.update u s p.1) t p.2) with hG
  have hGos : IsOsgood2_dev G := by
    refine ⟨?_, fun b => ?_, fun a => ?_⟩
    · refine hf.1.comp (continuous_pi fun i => ?_)
      by_cases hit : i = t
      · subst hit
        simp only [Function.update_self]
        exact continuous_snd
      · by_cases his : i = s
        · subst his
          simp only [Function.update_of_ne hit, Function.update_self]
          exact continuous_fst
        · simp only [Function.update_of_ne hit, Function.update_of_ne his]
          exact continuous_const
    · have e : (fun a => G (a, b)) = fun a => f (Function.update (Function.update u t b) s a) :=
        funext fun a => by simp only [hG]; rw [Function.update_comm hst]
      rw [e]
      exact hf.2 _ s
    · exact hf.2 (Function.update u s a) t
  have hGf : HasFDerivAt G (fderiv ℂ G (u s, u t)) (u s, u t) :=
    (isOsgood2_differentiable_dev hGos (u s, u t)).hasFDerivAt
  set G' := fderiv ℂ G (u s, u t) with hG'
  have h1 : HasDerivAt (fun a => f (Function.update u s a)) (G' ((1 : ℂ), (0 : ℂ))) (u s) := by
    have hcur : HasDerivAt (fun a : ℂ => (a, u t)) ((1 : ℂ), (0 : ℂ)) (u s) :=
      (hasDerivAt_id (u s)).prodMk (hasDerivAt_const (u s) (u t))
    refine (hGf.comp_hasDerivAt_of_eq (u s) hcur rfl).congr_of_eventuallyEq (Filter.Eventually.of_forall fun a => ?_)
    show f (Function.update u s a) = f (Function.update (Function.update u s a) t (u t))
    rw [show u t = Function.update u s a t from (Function.update_of_ne hst.symm a u).symm, Function.update_eq_self]
  have h2 : HasDerivAt (fun b => f (Function.update u t b)) (G' ((0 : ℂ), (1 : ℂ))) (u t) := by
    have hcur : HasDerivAt (fun b : ℂ => (u s, b)) ((0 : ℂ), (1 : ℂ)) (u t) :=
      (hasDerivAt_const (u t) (u s)).prodMk (hasDerivAt_id (u t))
    refine (hGf.comp_hasDerivAt_of_eq (u t) hcur rfl).congr_of_eventuallyEq (Filter.Eventually.of_forall fun b => ?_)
    show f (Function.update u t b) = f (Function.update (Function.update u s (u s)) t b)
    rw [Function.update_eq_self]
  have hc : HasDerivAt (fun v : ℂ => f (Function.update (Function.update u s (u s + v / 2)) t (u t - v / 2)))
      (G' ((1 / 2 : ℂ), -(1 / 2 : ℂ))) 0 := by
    have hcur : HasDerivAt (fun v : ℂ => (u s + v / 2, u t - v / 2)) ((1 / 2 : ℂ), -(1 / 2 : ℂ)) 0 := by
      refine HasDerivAt.prodMk ?_ ?_
      · simpa using ((hasDerivAt_id (0 : ℂ)).div_const 2).const_add (u s)
      · simpa using ((hasDerivAt_id (0 : ℂ)).div_const 2).const_sub (u t)
    exact hGf.comp_hasDerivAt_of_eq (0 : ℂ) hcur (by simp)
  have hlin : G' ((1 / 2 : ℂ), -(1 / 2 : ℂ)) = (1 / 2 : ℂ) * G' ((1 : ℂ), (0 : ℂ)) - (1 / 2 : ℂ) * G' ((0 : ℂ), (1 : ℂ)) := by
    have e : ((1 / 2 : ℂ), -(1 / 2 : ℂ)) = (1 / 2 : ℂ) • ((1 : ℂ), (0 : ℂ)) - (1 / 2 : ℂ) • ((0 : ℂ), (1 : ℂ)) := by
      ext <;> simp
    rw [e, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  unfold relDeriv
  rw [h1.deriv, h2.deriv, hc.deriv, hlin]
  ring

/-! ### Proof devices for the numerators (proof phase, round two; not statements of the paper)

The paper: "`$J^2g$ has no poles along any divisor, so it is holomorphic.`" The numerator is written down: `℘_ε ϑ₁²` has
order `−2 + 2 = 0` at every lattice point (Lemma C.theta(c)–(e)), so it has an entire representative `regE_dev`
(Mathlib's `MeromorphicAt.meromorphicOrderAt_nonneg_iff` at each lattice point, glued with `not_mem_Λu_punctured_dev`);
`J = J(x) J(y) ∏_{a,k} ϑ₁(x_a − y_k)` (`Jfun_append_dev`); multiplying row `a` of the determinant by
`∏_k ϑ₁(x_a − y_k)²` (`Matrix.det_mul_column`) turns every entry into an entire function (`regEntry_dev`, or the row
factor itself in a column of ones). The numerator is then a polynomial in entire functions of linear forms, hence
Fréchet differentiable on `ℂ^N`, hence in the Osgood class (`isOsgood_of_differentiable_dev`). -/

/-- `g_{2m+1}` is the determinant of the `℘`-matrix of `(x, y ⧺ c)` with its last column replaced by ones (any `c`). -/
theorem gOdd_eq_updateCol_dev (τ : ℍ) (m : ℕ) (x : Fin (m + 1) → ℂ) (y : Fin m → ℂ) (c : ℂ) :
    gOdd τ m x y = ((Matrix.of fun (a k : Fin (m + 1)) => wp τ (x a - (Fin.snoc y c : Fin (m + 1) → ℂ) k)).updateCol
      (Fin.last m) fun _ => 1).det := by
  unfold gOdd
  congr 1
  ext a k
  simp only [Matrix.of_apply, Matrix.updateCol_apply]
  refine Fin.lastCases ?_ (fun k' => ?_) k
  · simp
  · have hk : (Fin.castSucc k' : Fin (m + 1)) ≠ Fin.last m := (Fin.castSucc_lt_last k').ne
    simp [hk, Fin.snoc_castSucc]

theorem not_mem_Λu_nhds_dev (τ : ℍ) {z : ℂ} (hz : z ∉ Λu τ) : ∀ᶠ w in 𝓝 z, w ∉ Λu τ := by
  have h0 : theta1 z τ ≠ 0 := fun h => hz ((theta1_eq_zero_iff τ z).1 h)
  filter_upwards [(theta1_differentiable τ).continuous.continuousAt.eventually_ne h0] with w hw
  exact fun hmem => hw ((theta1_eq_zero_iff τ w).2 hmem)

theorem not_mem_Λu_punctured_dev (τ : ℍ) {l : ℂ} (hl : l ∈ Λu τ) : ∀ᶠ w in 𝓝[≠] l, w ∉ Λu τ := by
  have ha : AnalyticAt ℂ (fun w => theta1 w τ) l := (theta1_differentiable τ).analyticAt l
  rcases ha.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hd : deriv (fun w => theta1 w τ) l = 0 := by
      rw [Filter.EventuallyEq.deriv_eq (f₁ := fun w => theta1 w τ) (f := fun _ => (0 : ℂ)) h]
      simp
    exact theta1_deriv_ne_zero_of_mem τ hl hd
  · filter_upwards [h] with w hw
    exact fun hmem => hw ((theta1_eq_zero_iff τ w).2 hmem)

theorem zero_mem_Λu_dev (τ : ℍ) : (0 : ℂ) ∈ Λu τ := ⟨0, 0, by simp⟩

theorem Λu_countable_dev (τ : ℍ) : (Λu τ).Countable := by
  have h : Λu τ ⊆ Set.range (fun pq : ℤ × ℤ => (pq.1 : ℂ) + pq.2 * (τ : ℂ)) := by
    rintro u ⟨p, q, rfl⟩
    exact ⟨(p, q), rfl⟩
  exact (Set.countable_range _).mono h

/-- No up–down difference on the lattice. -/
def Generic_dev (τ : ℍ) {n m : ℕ} (x : Fin n → ℂ) (y : Fin m → ℂ) : Prop :=
  ∀ a k, x a - y k ∉ Λu τ

theorem neg_mem_Λu_dev (τ : ℍ) {z : ℂ} (hz : z ∈ Λu τ) : -z ∈ Λu τ := by
  obtain ⟨p, q, rfl⟩ := hz
  exact ⟨-p, -q, by push_cast; ring⟩

theorem exists_reg_dev (τ : ℍ) (ε : Eps) :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ ∀ w, w ∉ Λu τ → E w = wpE τ ε w * theta1 w τ ^ 2 := by
  classical
  set h : ℂ → ℂ := fun w => wpE τ ε w * theta1 w τ ^ 2 with hh
  have hloc : ∀ l ∈ Λu τ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g l ∧ h =ᶠ[𝓝[≠] l] g := by
    intro l hl
    have hθd := theta1_differentiable τ
    have hθm : MeromorphicAt (fun w => theta1 w τ) l := (hθd.analyticAt l).meromorphicAt
    have hθ1 : meromorphicOrderAt (fun w => theta1 w τ) l = ((1 : ℤ) : WithTop ℤ) := by
      rw [meromorphicOrderAt_eq_int_iff hθm]
      refine ⟨dslope (fun w => theta1 w τ) l, ?_, ?_, Filter.Eventually.of_forall fun z => ?_⟩
      · have hd := (differentiableOn_dslope (s := Set.univ) (c := l) Filter.univ_mem).2 hθd.differentiableOn
        exact hd.analyticAt Filter.univ_mem
      · rw [dslope_same]
        exact theta1_deriv_ne_zero_of_mem τ hl
      · have h1 := sub_smul_dslope (fun w => theta1 w τ) l z
        have h0 : theta1 l τ = 0 := (theta1_eq_zero_iff τ l).2 hl
        simp only [h0, sub_zero, smul_eq_mul] at h1
        rw [zpow_one, smul_eq_mul, h1]
    have hwm : MeromorphicAt (wpE τ ε) l := wpE_meromorphic τ ε l
    have hwo : meromorphicOrderAt (wpE τ ε) l = ((-2 : ℤ) : WithTop ℤ) := by
      by_cases hε : ε = .pp
      · subst hε
        exact wp_order τ hl
      · exact wpE_order τ hε hl
    have hm : MeromorphicAt h l := hwm.fun_mul (hθm.fun_pow 2)
    have hord : meromorphicOrderAt h l = 0 := by
      rw [hh, fun_meromorphicOrderAt_mul hwm (hθm.fun_pow 2), fun_meromorphicOrderAt_pow hθm, hwo, hθ1]
      rfl
    exact (MeromorphicAt.meromorphicOrderAt_nonneg_iff hm).1 hord.ge
  choose g hg using hloc
  refine ⟨fun w => if hw : w ∈ Λu τ then g w hw w else h w, ?_, fun w hw => by simp [hw, hh]⟩
  intro z
  by_cases hz : z ∈ Λu τ
  · have heq : (fun w => if hw : w ∈ Λu τ then g w hw w else h w) =ᶠ[𝓝 z] g z hz := by
      rw [← nhdsNE_sup_pure z]
      refine Filter.eventually_sup.2 ⟨?_, ?_⟩
      · filter_upwards [not_mem_Λu_punctured_dev τ hz, (hg z hz).2] with w hw hgw
        simp only [hw, dite_false]
        exact hgw
      · exact Filter.eventually_pure.2 (by simp [hz])
    exact ((hg z hz).1.differentiableAt).congr_of_eventuallyEq heq
  · have heq : (fun w => if hw : w ∈ Λu τ then g w hw w else h w) =ᶠ[𝓝 z] h := by
      filter_upwards [not_mem_Λu_nhds_dev τ hz] with w hw
      simp [hw]
    have hd : DifferentiableAt ℂ h z :=
      ((wpE_analyticAt τ ε hz).differentiableAt).mul (((theta1_differentiable τ) z).pow 2)
    exact hd.congr_of_eventuallyEq heq

/-- The entire representative of `℘_ε ϑ₁²`. -/
def regE_dev (τ : ℍ) (ε : Eps) : ℂ → ℂ := Classical.choose (exists_reg_dev τ ε)

theorem regE_differentiable_dev (τ : ℍ) (ε : Eps) : Differentiable ℂ (regE_dev τ ε) :=
  (Classical.choose_spec (exists_reg_dev τ ε)).1

theorem regE_eq_dev (τ : ℍ) (ε : Eps) {w : ℂ} (hw : w ∉ Λu τ) :
    regE_dev τ ε w = wpE τ ε w * theta1 w τ ^ 2 :=
  (Classical.choose_spec (exists_reg_dev τ ε)).2 w hw

/-- `J(x ⧺ y) = J(x) J(y) ∏_{a,k} ϑ₁(x_a − y_k)`. -/
theorem Jfun_append_dev (τ : ℂ) {n m : ℕ} (u : Fin (n + m) → ℂ) :
    Jfun τ u = Jfun τ (fun a => u (Fin.castAdd m a)) * Jfun τ (fun k => u (Fin.natAdd n k)) *
      ∏ a : Fin n, ∏ k : Fin m, theta1 (u (Fin.castAdd m a) - u (Fin.natAdd n k)) τ := by
  have h1 : ∀ (a : Fin n) (k : Fin m), Fin.castAdd m a < Fin.natAdd n k := fun a k => by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have h2 : ∀ (a : Fin n) (k : Fin m), ¬ Fin.natAdd n k < Fin.castAdd m a := fun a k => by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have h3 : ∀ a b : Fin n, Fin.castAdd m a < Fin.castAdd m b ↔ a < b := fun a b => by
    simp only [Fin.lt_def, Fin.val_castAdd]
  have h4 : ∀ k l : Fin m, Fin.natAdd n k < Fin.natAdd n l ↔ k < l := fun k l => by
    simp only [Fin.lt_def, Fin.val_natAdd]
    omega
  unfold Jfun
  simp only [Finset.prod_filter]
  rw [Fin.prod_univ_add]
  simp only [Fin.prod_univ_add, h1, h2, h3, h4, ite_true, ite_false, Finset.prod_const_one, one_mul]
  rw [Finset.prod_mul_distrib]
  ring

theorem differentiable_finsetProd_dev {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Finset ι)
    {f : ι → E → ℂ} (h : ∀ i ∈ s, Differentiable ℂ (f i)) : Differentiable ℂ (fun x => ∏ i ∈ s, f i x) := by
  have hp := Finset.prod_induction (fun i => f i) (fun g : E → ℂ => Differentiable ℂ g)
    (fun a b ha hb => ha.mul hb) (differentiable_const 1) h
  convert hp using 1
  funext x
  simp [Finset.prod_apply]

theorem differentiable_det_dev {n N : ℕ} (E : Fin n → Fin n → (Fin N → ℂ) → ℂ)
    (hE : ∀ i j, Differentiable ℂ (E i j)) : Differentiable ℂ (fun u => (Matrix.of fun i j => E i j u).det) := by
  have e : (fun u => (Matrix.of fun i j => E i j u).det) =
      fun u => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, E (σ i) i u := by
    funext u
    rw [Matrix.det_apply']
    simp
  rw [e]
  exact Differentiable.fun_sum fun σ _ =>
    (differentiable_const _).mul (differentiable_finsetProd_dev _ fun i _ => hE (σ i) i)

theorem isOsgood_of_differentiable_dev {N : ℕ} {f : (Fin N → ℂ) → ℂ} (hf : Differentiable ℂ f) : IsOsgood f :=
  ⟨hf.continuous, fun u i => hf.comp (differentiable_pi.2 fun a => differentiable_update_apply_dev u i a)⟩

theorem differentiable_theta1_sub_dev (τ : ℍ) {N : ℕ} (i j : Fin N) :
    Differentiable ℂ fun u : Fin N → ℂ => theta1 (u i - u j) τ :=
  (theta1_differentiable τ).comp ((differentiable_apply i).sub (differentiable_apply j))

theorem differentiable_Jfun_comp_dev (τ : ℍ) {N n : ℕ} (e : Fin n → Fin N) :
    Differentiable ℂ fun u : Fin N → ℂ => Jfun τ (fun a => u (e a)) := by
  unfold Jfun
  exact differentiable_finsetProd_dev _ fun a _ => differentiable_finsetProd_dev _ fun b _ =>
    differentiable_theta1_sub_dev τ (e a) (e b)

theorem differentiable_F_sum_dev {N : ℕ} {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ fun u : Fin N → ℂ => F (∑ i, u i) :=
  hF.comp (Differentiable.fun_sum fun i _ => differentiable_apply i)

/-- The row factor `∏_k ϑ₁(x_a − y_k)²`. -/
def rowTheta_dev (τ : ℍ) {n m : ℕ} (x : Fin n → ℂ) (y : Fin m → ℂ) (a : Fin n) : ℂ :=
  ∏ k, theta1 (x a - y k) τ ^ 2

/-- The regularized entry `℘̂_ε(x_a − y_k) ∏_{k' ≠ k} ϑ₁(x_a − y_{k'})²`. -/
def regEntry_dev (τ : ℍ) (ε : Eps) {n m : ℕ} (x : Fin n → ℂ) (y : Fin m → ℂ) (a : Fin n) (k : Fin m) : ℂ :=
  regE_dev τ ε (x a - y k) * ∏ k' ∈ Finset.univ.erase k, theta1 (x a - y k') τ ^ 2

theorem regEntry_eq_dev (τ : ℍ) (ε : Eps) {n m : ℕ} (x : Fin n → ℂ) (y : Fin m → ℂ) (a : Fin n) (k : Fin m)
    (h : x a - y k ∉ Λu τ) : regEntry_dev τ ε x y a k = rowTheta_dev τ x y a * wpE τ ε (x a - y k) := by
  unfold regEntry_dev rowTheta_dev
  rw [regE_eq_dev τ ε h, ← Finset.mul_prod_erase Finset.univ (fun k' => theta1 (x a - y k') τ ^ 2)
    (Finset.mem_univ k)]
  ring

theorem prod_rowTheta_dev (τ : ℍ) {n m : ℕ} (x : Fin n → ℂ) (y : Fin m → ℂ) :
    ∏ a, rowTheta_dev τ x y a = (∏ a, ∏ k, theta1 (x a - y k) τ) ^ 2 := by
  simp only [rowTheta_dev, Finset.prod_pow]

theorem differentiable_rowTheta_dev (τ : ℍ) {N n m : ℕ} (ex : Fin n → Fin N) (ey : Fin m → Fin N) (a : Fin n) :
    Differentiable ℂ fun u : Fin N → ℂ => rowTheta_dev τ (fun a => u (ex a)) (fun k => u (ey k)) a := by
  unfold rowTheta_dev
  exact differentiable_finsetProd_dev _ fun k _ => (differentiable_theta1_sub_dev τ (ex a) (ey k)).pow 2

theorem differentiable_regEntry_dev (τ : ℍ) (ε : Eps) {N n m : ℕ} (ex : Fin n → Fin N) (ey : Fin m → Fin N)
    (a : Fin n) (k : Fin m) :
    Differentiable ℂ fun u : Fin N → ℂ => regEntry_dev τ ε (fun a => u (ex a)) (fun k => u (ey k)) a k := by
  unfold regEntry_dev
  exact ((regE_differentiable_dev τ ε).comp ((differentiable_apply (ex a)).sub (differentiable_apply (ey k)))).mul
    (differentiable_finsetProd_dev _ fun k' _ => (differentiable_theta1_sub_dev τ (ex a) (ey k')).pow 2)

/-- Off the polar set, the state is `F(U) J(x)² J(y)² ∏_a (row factor) · g`. -/
theorem stateFun_eq_dev (τ : ℍ) {n m : ℕ} (F : ℂ → ℂ) (g : (Fin n → ℂ) → (Fin m → ℂ) → ℂ)
    (u : Fin (n + m) → ℂ) :
    stateFun τ F g u = F (∑ i, u i) * Jfun τ (fun a => u (Fin.castAdd m a)) ^ 2 *
      Jfun τ (fun k => u (Fin.natAdd n k)) ^ 2 *
        ((∏ a, rowTheta_dev τ (fun a => u (Fin.castAdd m a)) (fun k => u (Fin.natAdd n k)) a) *
          g (fun a => u (Fin.castAdd m a)) (fun k => u (Fin.natAdd n k))) := by
  unfold stateFun
  rw [Jfun_append_dev τ u, prod_rowTheta_dev]
  ring

/-- A branch on a fixed proposition of two differentiable functions. -/
theorem differentiable_ite_dev {N : ℕ} (p : Prop) [Decidable p] {A B : (Fin N → ℂ) → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) : Differentiable ℂ fun u => if p then A u else B u := by
  by_cases hp : p
  · simpa [hp] using hA
  · simpa [hp] using hB

theorem prod_rowTheta_swap_dev (τ : ℍ) {n m : ℕ} (x : Fin n → ℂ) (y : Fin m → ℂ) :
    ∏ a, rowTheta_dev τ x y a = ∏ k, rowTheta_dev τ y x k := by
  unfold rowTheta_dev
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun a _ => ?_
  rw [← theta1_sq_neg_dev, neg_sub]

/-! ### Proof devices for the shape of the numerators (proof phase, round two; not statements of the paper)

A continuous function vanishing off the polar set vanishes (`eq_zero_of_offPolar_dev`: the line `u + t·(0, 𝟙)` meets
the polar set for only countably many `t`). The identities of `IsCanonShape` — the multipliers of each variable at
`L = 2N` and the antisymmetry within a species — hold for `F(U) J² g` off the polar set, from the multipliers of
`Θ_2[ε]`, those of `J²` (Lemma C.theta(f)) and conditions (ii)–(iii) for `g`; so they hold for the numerator everywhere
(`shape_of_numerator_dev`). -/

theorem mem_Λu_of_add_dev (τ : ℍ) {z l : ℂ} (hl : l ∈ Λu τ) (h : z + l ∈ Λu τ) : z ∈ Λu τ := by
  obtain ⟨p, q, hpq⟩ := h
  obtain ⟨p', q', rfl⟩ := hl
  exact ⟨p - p', q - q', by push_cast; linear_combination hpq⟩

theorem add_mem_Λu_dev (τ : ℍ) {z l : ℂ} (hz : z ∈ Λu τ) (hl : l ∈ Λu τ) : z + l ∈ Λu τ := by
  obtain ⟨p, q, rfl⟩ := hz
  obtain ⟨p', q', rfl⟩ := hl
  exact ⟨p + p', q + q', by push_cast; ring⟩

theorem one_mem_Λu_dev (τ : ℍ) : (1 : ℂ) ∈ Λu τ := ⟨1, 0, by simp⟩

theorem tau_mem_Λu_dev (τ : ℍ) : (τ : ℂ) ∈ Λu τ := ⟨0, 1, by simp⟩

/-- A continuous function vanishing off the polar set vanishes. -/
theorem eq_zero_of_offPolar_dev (τ : ℍ) {n m : ℕ} {φ : (Fin (n + m) → ℂ) → ℂ} (hφ : Continuous φ)
    (h : ∀ u, u ∉ polarSet τ n m → φ u = 0) : φ = 0 := by
  funext u
  let δ : Fin (n + m) → ℂ := Fin.append (fun _ => 0) (fun _ => 1)
  let line : ℂ → (Fin (n + m) → ℂ) := fun t => u + t • δ
  have hline : Continuous line := continuous_const.add (continuous_id.smul continuous_const)
  have hSc : (⋃ a : Fin n, ⋃ k : Fin m,
      (fun l => u (Fin.castAdd m a) - u (Fin.natAdd n k) - l) '' Λu τ).Countable :=
    Set.countable_iUnion fun a => Set.countable_iUnion fun k => (Λu_countable_dev τ).image _
  have hoff : ∀ t ∉ (⋃ a : Fin n, ⋃ k : Fin m,
      (fun l => u (Fin.castAdd m a) - u (Fin.natAdd n k) - l) '' Λu τ), line t ∉ polarSet τ n m := by
    rintro t ht ⟨a, k, hmem⟩
    apply ht
    refine Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨k, ⟨_, hmem, ?_⟩⟩⟩
    show u (Fin.castAdd m a) - u (Fin.natAdd n k) - (line t (Fin.castAdd m a) - line t (Fin.natAdd n k)) = t
    simp only [line, δ, Pi.add_apply, Pi.smul_apply, Fin.append_left, Fin.append_right, smul_eq_mul]
    ring
  have hz : (fun t => φ (line t)) = fun _ => 0 :=
    Continuous.ext_on (hSc.dense_compl ℂ) (hφ.comp hline) continuous_const fun t ht => h _ (hoff t ht)
  have := congrFun hz 0
  simpa [line] using this

theorem sum_update_add_dev {N : ℕ} (v : Fin N → ℂ) (i : Fin N) (c : ℂ) :
    ∑ j, Function.update v i (v i + c) j = ∑ j, v j + c := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase _ v (Finset.mem_univ i)]
  ring

theorem castAdd_update_dev {n m : ℕ} (v : Fin (n + m) → ℂ) (a : Fin n) (z : ℂ) :
    (fun a' => Function.update v (Fin.castAdd m a) z (Fin.castAdd m a')) =
      Function.update (fun a' => v (Fin.castAdd m a')) a z := by
  funext a'
  by_cases h : a' = a
  · subst h
    simp
  · rw [Function.update_of_ne ((Fin.castAdd_injective n m).ne h), Function.update_of_ne h]

theorem natAdd_update_castAdd_dev {n m : ℕ} (v : Fin (n + m) → ℂ) (a : Fin n) (z : ℂ) :
    (fun k => Function.update v (Fin.castAdd m a) z (Fin.natAdd n k)) = fun k => v (Fin.natAdd n k) := by
  funext k
  rw [Function.update_of_ne (castAdd_ne_natAdd_dev a k).symm]

theorem natAdd_update_dev {n m : ℕ} (v : Fin (n + m) → ℂ) (k : Fin m) (z : ℂ) :
    (fun k' => Function.update v (Fin.natAdd n k) z (Fin.natAdd n k')) =
      Function.update (fun k' => v (Fin.natAdd n k')) k z := by
  funext k'
  by_cases h : k' = k
  · subst h
    simp
  · rw [Function.update_of_ne ((Fin.natAdd_injective m n).ne h), Function.update_of_ne h]

theorem castAdd_update_natAdd_dev {n m : ℕ} (v : Fin (n + m) → ℂ) (k : Fin m) (z : ℂ) :
    (fun a => Function.update v (Fin.natAdd n k) z (Fin.castAdd m a)) = fun a => v (Fin.castAdd m a) := by
  funext a
  rw [Function.update_of_ne (castAdd_ne_natAdd_dev a k)]

/-- Shifting one variable by a lattice vector preserves the complement of the polar set. -/
theorem update_not_mem_polar_dev (τ : ℍ) {n m : ℕ} (v : Fin (n + m) → ℂ) (i : Fin (n + m)) {l : ℂ}
    (hl : l ∈ Λu τ) (hv : v ∉ polarSet τ n m) : Function.update v i (v i + l) ∉ polarSet τ n m := by
  rintro ⟨a, k, hmem⟩
  apply hv
  refine ⟨a, k, ?_⟩
  induction i using Fin.addCases with
  | left a' =>
    by_cases ha : a = a'
    · subst ha
      rw [Function.update_self, Function.update_of_ne (castAdd_ne_natAdd_dev a k).symm] at hmem
      exact mem_Λu_of_add_dev τ hl (by
        rw [show v (Fin.castAdd m a) - v (Fin.natAdd n k) + l = v (Fin.castAdd m a) + l - v (Fin.natAdd n k) by
          ring]
        exact hmem)
    · rwa [Function.update_of_ne ((Fin.castAdd_injective n m).ne ha),
        Function.update_of_ne (castAdd_ne_natAdd_dev a' k).symm] at hmem
  | right k' =>
    by_cases hk : k = k'
    · subst hk
      rw [Function.update_self, Function.update_of_ne (castAdd_ne_natAdd_dev a k)] at hmem
      have h := add_mem_Λu_dev τ hmem hl
      rwa [show v (Fin.castAdd m a) - (v (Fin.natAdd n k) + l) + l = v (Fin.castAdd m a) - v (Fin.natAdd n k) by
        ring] at h
    · rwa [Function.update_of_ne (castAdd_ne_natAdd_dev a k'),
        Function.update_of_ne ((Fin.natAdd_injective m n).ne hk)] at hmem

theorem continuous_update_add_dev {N : ℕ} (i : Fin N) (c : ℂ) :
    Continuous fun v : Fin N → ℂ => Function.update v i (v i + c) :=
  continuous_id.update i ((continuous_apply i).add continuous_const)

/-- The shape of a numerator, from the multipliers and the antisymmetry of `g`. -/
theorem shape_of_numerator_dev (τ : ℍ) {n m : ℕ} (ε : Eps) {F : ℂ → ℂ} (hF : F ∈ Θ2 τ ε)
    (g : (Fin n → ℂ) → (Fin m → ℂ) → ℂ)
    (hx1 : ∀ x y a, g (Function.update x a (x a + 1)) y = ε.e1 * g x y)
    (hxτ : ∀ x y a, g (Function.update x a (x a + τ)) y = ε.e2 * g x y)
    (hy1 : ∀ x y k, g x (Function.update y k (y k + 1)) = ε.e1 * g x y)
    (hyτ : ∀ x y k, g x (Function.update y k (y k + τ)) = ε.e2 * g x y)
    (hxs : ∀ x y a b, a ≠ b → g (x ∘ Equiv.swap a b) y = -g x y)
    (hys : ∀ x y k l, k ≠ l → g x (y ∘ Equiv.swap k l) = -g x y)
    {f : (Fin (n + m) → ℂ) → ℂ} (hf : IsNumerator τ n m F g f) : IsCanonShape τ (2 * (n + m)) n m f := by
  have he1 : (ε.e1)⁻¹ = ε.e1 := by cases ε <;> norm_num [Eps.e1]
  have he2 : (ε.e2)⁻¹ = ε.e2 := by cases ε <;> norm_num [Eps.e2]
  have hg1 : ∀ (v : Fin (n + m) → ℂ) (i : Fin (n + m)),
      g (fun a => Function.update v i (v i + 1) (Fin.castAdd m a))
        (fun k => Function.update v i (v i + 1) (Fin.natAdd n k)) =
        ε.e1 * g (fun a => v (Fin.castAdd m a)) (fun k => v (Fin.natAdd n k)) := by
    intro v i
    induction i using Fin.addCases with
    | left a =>
      rw [castAdd_update_dev, natAdd_update_castAdd_dev]
      exact hx1 _ _ _
    | right k =>
      rw [castAdd_update_natAdd_dev, natAdd_update_dev]
      exact hy1 _ _ _
  have hgτ : ∀ (v : Fin (n + m) → ℂ) (i : Fin (n + m)),
      g (fun a => Function.update v i (v i + τ) (Fin.castAdd m a))
        (fun k => Function.update v i (v i + τ) (Fin.natAdd n k)) =
        ε.e2 * g (fun a => v (Fin.castAdd m a)) (fun k => v (Fin.natAdd n k)) := by
    intro v i
    induction i using Fin.addCases with
    | left a =>
      rw [castAdd_update_dev, natAdd_update_castAdd_dev]
      exact hxτ _ _ _
    | right k =>
      rw [castAdd_update_natAdd_dev, natAdd_update_dev]
      exact hyτ _ _ _
  have hF1 : ∀ U, F (U + 1) = (ε.e1)⁻¹ * F U := hF.2.1
  have hFτ : ∀ U, F (U + τ) = (ε.e2)⁻¹ * cexp (-4 * π * I * U - 2 * π * I * τ) * F U := hF.2.2
  -- the identities off the polar set, then everywhere
  have hP1 : ∀ (i : Fin (n + m)) (v : Fin (n + m) → ℂ), f (Function.update v i (v i + 1)) = f v := by
    intro i
    have h := eq_zero_of_offPolar_dev τ (φ := fun v => f (Function.update v i (v i + 1)) - f v)
      ((hf.1.1.comp (continuous_update_add_dev i 1)).sub hf.1.1) fun v hv => by
        rw [hf.2 _ (update_not_mem_polar_dev τ v i (one_mem_Λu_dev τ) hv), hf.2 v hv]
        unfold stateFun
        rw [sum_update_add_dev, hF1, Jfun_sq_add_one, hg1, he1]
        have := e1_mul_self_dev ε
        linear_combination (F (∑ j, v j) * Jfun τ v ^ 2 *
          g (fun a => v (Fin.castAdd m a)) (fun k => v (Fin.natAdd n k))) * this
    intro v
    have := congrFun h v
    simp only [Pi.zero_apply] at this
    linear_combination this
  have hPτ : ∀ (i : Fin (n + m)) (v : Fin (n + m) → ℂ), f (Function.update v i (v i + τ)) =
      cexp (-π * I * ((2 * (n + m) : ℕ) : ℂ) * (2 * v i + τ)) * f v := by
    intro i
    have h := eq_zero_of_offPolar_dev τ
      (φ := fun v => f (Function.update v i (v i + τ)) - cexp (-π * I * ((2 * (n + m) : ℕ) : ℂ) * (2 * v i + τ)) * f v)
      ((hf.1.1.comp (continuous_update_add_dev i τ)).sub ((by fun_prop : Continuous fun v : Fin (n + m) → ℂ =>
        cexp (-π * I * ((2 * (n + m) : ℕ) : ℂ) * (2 * v i + τ))).mul hf.1.1)) fun v hv => by
        rw [hf.2 _ (update_not_mem_polar_dev τ v i (tau_mem_Λu_dev τ) hv), hf.2 v hv]
        unfold stateFun
        rw [sum_update_add_dev, hFτ, Jfun_sq_add_tau, hgτ, he2]
        have h2 := e2_mul_self_dev ε
        have hexp : cexp (-4 * π * I * (∑ j, v j) - 2 * π * I * τ) *
            cexp (-2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ - 4 * π * I * (((n + m : ℕ) : ℂ) * v i - ∑ j, v j)) =
            cexp (-π * I * ((2 * (n + m) : ℕ) : ℂ) * (2 * v i + τ)) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        linear_combination (F (∑ j, v j) * Jfun τ v ^ 2 *
            g (fun a => v (Fin.castAdd m a)) (fun k => v (Fin.natAdd n k))) *
          (cexp (-4 * π * I * (∑ j, v j) - 2 * π * I * τ) *
            cexp (-2 * π * I * (((n + m : ℕ) : ℂ) - 1) * τ - 4 * π * I * (((n + m : ℕ) : ℂ) * v i - ∑ j, v j)) *
              h2 + hexp)
    intro v
    have := congrFun h v
    simp only [Pi.zero_apply] at this
    linear_combination this
  have hanti : ∀ s t : Fin (n + m), s ≠ t → SameSpecies n s t → ∀ v, f (v ∘ Equiv.swap s t) = -f v := by
    intro s t hst hss
    have hsw : ∀ v : Fin (n + m) → ℂ,
        g (fun a => v (Equiv.swap s t (Fin.castAdd m a))) (fun k => v (Equiv.swap s t (Fin.natAdd n k))) =
          -g (fun a => v (Fin.castAdd m a)) (fun k => v (Fin.natAdd n k)) ∧
        (v ∉ polarSet τ n m → v ∘ Equiv.swap s t ∉ polarSet τ n m) := by
      intro v
      induction s using Fin.addCases with
      | left a =>
        induction t using Fin.addCases with
        | left b =>
          have hab : a ≠ b := fun h => hst (by rw [h])
          have hx : (fun a' => v (Equiv.swap (Fin.castAdd m a) (Fin.castAdd m b) (Fin.castAdd m a'))) =
              (fun a' => v (Fin.castAdd m a')) ∘ Equiv.swap a b := by
            funext a'
            rw [Function.comp_apply, (Fin.castAdd_injective n m).swap_apply]
          have hy : (fun k => v (Equiv.swap (Fin.castAdd m a) (Fin.castAdd m b) (Fin.natAdd n k))) =
              fun k => v (Fin.natAdd n k) := by
            funext k
            rw [Equiv.swap_apply_of_ne_of_ne (castAdd_ne_natAdd_dev _ _).symm (castAdd_ne_natAdd_dev _ _).symm]
          refine ⟨by rw [hx, hy, hxs _ _ _ _ hab], fun hv ⟨a', k, hmem⟩ => hv ⟨Equiv.swap a b a', k, ?_⟩⟩
          simp only [Function.comp_apply] at hmem
          rwa [(Fin.castAdd_injective n m).swap_apply,
            Equiv.swap_apply_of_ne_of_ne (castAdd_ne_natAdd_dev _ _).symm (castAdd_ne_natAdd_dev _ _).symm] at hmem
        | right l =>
          have hss' : ((Fin.castAdd m a : Fin (n + m)) : ℕ) < n ↔ ((Fin.natAdd n l : Fin (n + m)) : ℕ) < n := hss
          simp only [Fin.val_castAdd, Fin.val_natAdd, a.isLt, true_iff] at hss'
          omega
      | right k =>
        induction t using Fin.addCases with
        | left b =>
          have hss' : ((Fin.natAdd n k : Fin (n + m)) : ℕ) < n ↔ ((Fin.castAdd m b : Fin (n + m)) : ℕ) < n := hss
          simp only [Fin.val_castAdd, Fin.val_natAdd, b.isLt, iff_true] at hss'
          omega
        | right l =>
          have hkl : k ≠ l := fun h => hst (by rw [h])
          have hx : (fun a => v (Equiv.swap (Fin.natAdd n k) (Fin.natAdd n l) (Fin.castAdd m a))) =
              fun a => v (Fin.castAdd m a) := by
            funext a
            rw [Equiv.swap_apply_of_ne_of_ne (castAdd_ne_natAdd_dev _ _) (castAdd_ne_natAdd_dev _ _)]
          have hy : (fun k' => v (Equiv.swap (Fin.natAdd n k) (Fin.natAdd n l) (Fin.natAdd n k'))) =
              (fun k' => v (Fin.natAdd n k')) ∘ Equiv.swap k l := by
            funext k'
            rw [Function.comp_apply, (Fin.natAdd_injective m n).swap_apply]
          refine ⟨by rw [hx, hy, hys _ _ _ _ hkl], fun hv ⟨a, k', hmem⟩ => hv ⟨a, Equiv.swap k l k', ?_⟩⟩
          simp only [Function.comp_apply] at hmem
          rwa [(Fin.natAdd_injective m n).swap_apply,
            Equiv.swap_apply_of_ne_of_ne (castAdd_ne_natAdd_dev _ _) (castAdd_ne_natAdd_dev _ _)] at hmem
    have h := eq_zero_of_offPolar_dev τ (φ := fun v => f (v ∘ Equiv.swap s t) + f v)
      ((hf.1.1.comp (continuous_pi fun i => continuous_apply _)).add hf.1.1) fun v hv => by
        rw [hf.2 _ ((hsw v).2 hv), hf.2 v hv]
        unfold stateFun
        simp only [Function.comp_apply]
        rw [(hsw v).1, Jfun_sq_perm, Equiv.sum_comp]
        ring
    intro v
    have := congrFun h v
    simp only [Pi.zero_apply] at this
    linear_combination this
  refine ⟨hf.1, fun u i => ⟨hf.1.2 u i, fun z => ?_, fun z => ?_⟩, hanti⟩
  · have h := hP1 i (Function.update u i z)
    rw [Function.update_self, Function.update_idem] at h
    beta_reduce
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    exact h
  · have h := hPτ i (Function.update u i z)
    rw [Function.update_self, Function.update_idem] at h
    beta_reduce
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    exact h

/-! ### Proof devices for (C1) (proof phase, round two; not statements of the paper)

The paper's argument: "`(C1): $J^2$ vanishes to order $2$ on same-spin divisors and $g$ vanishes there, so $f$ vanishes to order $\ge3$.`"
Here in this form: the numerator is `J(x)² J(y)² R` with `R` in the Osgood class (the explicit numerators,
`*_numerator_factor_dev`, and their uniqueness, `numerator_unique_dev`); for two variables `s, t` of one species
`J² = ϑ₁(u_s − u_t)² K` (Lemma C.theta(f)), so `f = ϑ₁(u_s − u_t)² Q` with `Q` in the class; the antisymmetry of `f` under
the swap of `s, t` passes to `Q` (by continuity across `u_s − u_t ∈ Λ_u`), so `Q = 0` on `u_s = u_t`; the multipliers
of `f` and of `ϑ₁²` show that the zeros of `z ↦ Q(u with u_s := z)` are invariant under `Λ_u` (`vanishes3_core_dev`), and
a product `A B C` of three entire functions vanishing at `z₀` has its first two derivatives zero there
(`iteratedDeriv_mul3_dev`). -/

/-- A continuous function on `ℂ^N` vanishing wherever `u_s − u_t ∉ Λ_u` vanishes. -/
theorem eq_zero_of_offDiff_dev (τ : ℍ) {N : ℕ} {s t : Fin N} (hst : s ≠ t) {φ : (Fin N → ℂ) → ℂ}
    (hφ : Continuous φ) (h : ∀ u, u s - u t ∉ Λu τ → φ u = 0) : φ = 0 := by
  funext u
  let line : ℂ → (Fin N → ℂ) := fun c => Function.update u s (u s + c)
  have hline : Continuous line := continuous_const.update s (continuous_const.add continuous_id)
  have hSc : ((fun l => l - (u s - u t)) '' Λu τ).Countable := (Λu_countable_dev τ).image _
  have hz : (fun c => φ (line c)) = fun _ => 0 :=
    Continuous.ext_on (hSc.dense_compl ℂ) (hφ.comp hline) continuous_const fun c hc => h _ fun hmem =>
      hc ⟨_, hmem, by simp only [line, Function.update_self, Function.update_of_ne hst.symm]; ring⟩
  have := congrFun hz 0
  simpa [line] using this

theorem deriv_mul3_dev {A B C : ℂ → ℂ} (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (hC : Differentiable ℂ C) :
    deriv (fun z => A z * B z * C z) =
      fun z => deriv A z * B z * C z + A z * deriv B z * C z + A z * B z * deriv C z := by
  funext z
  exact (((hA z).hasDerivAt.mul (hB z).hasDerivAt).mul (hC z).hasDerivAt).deriv.trans (by simp only [Pi.mul_apply]; ring)

/-- A product of three entire functions vanishing at `z₀` has its value and first two derivatives zero there. -/
theorem iteratedDeriv_mul3_dev {A B C : ℂ → ℂ} (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (hC : Differentiable ℂ C) {z₀ : ℂ} (hA0 : A z₀ = 0) (hB0 : B z₀ = 0) (hC0 : C z₀ = 0) :
    ∀ j < 3, iteratedDeriv j (fun z => A z * B z * C z) z₀ = 0 := by
  have hd : ∀ {D : ℂ → ℂ}, Differentiable ℂ D → Differentiable ℂ (deriv D) := fun hD z =>
    ((hD.analyticAt z).deriv).differentiableAt
  intro j hj
  interval_cases j
  · simp [hA0]
  · rw [iteratedDeriv_one, deriv_mul3_dev hA hB hC]
    simp [hA0, hB0, hC0]
  · rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_mul3_dev hA hB hC]
    have t1 := ((hd hA z₀).hasDerivAt.mul (hB z₀).hasDerivAt).mul (hC z₀).hasDerivAt
    have t2 := ((hA z₀).hasDerivAt.mul (hd hB z₀).hasDerivAt).mul (hC z₀).hasDerivAt
    have t3 := ((hA z₀).hasDerivAt.mul (hB z₀).hasDerivAt).mul (hd hC z₀).hasDerivAt
    exact ((t1.add t2).add t3).deriv.trans (by simp only [Pi.mul_apply, hA0, hB0, hC0]; ring)

theorem isOsgood_mul_dev {N : ℕ} {f g : (Fin N → ℂ) → ℂ} (hf : IsOsgood f) (hg : IsOsgood g) :
    IsOsgood fun u => f u * g u :=
  ⟨hf.1.mul hg.1, fun u i => (hf.2 u i).mul (hg.2 u i)⟩

theorem isOsgood_comp_castAdd_dev {n m : ℕ} {K : (Fin n → ℂ) → ℂ} (hK : IsOsgood K) :
    IsOsgood fun u : Fin (n + m) → ℂ => K fun a => u (Fin.castAdd m a) := by
  refine ⟨hK.1.comp (continuous_pi fun a => continuous_apply _), fun u i => ?_⟩
  induction i using Fin.addCases with
  | left a =>
    have e : (fun z => K fun a' => Function.update u (Fin.castAdd m a) z (Fin.castAdd m a')) =
        fun z => K (Function.update (fun a' => u (Fin.castAdd m a')) a z) := by
      funext z
      rw [castAdd_update_dev]
    rw [e]
    exact hK.2 _ a
  | right k =>
    have e : (fun z => K fun a' => Function.update u (Fin.natAdd n k) z (Fin.castAdd m a')) =
        fun _ => K fun a' => u (Fin.castAdd m a') := by
      funext z
      rw [castAdd_update_natAdd_dev]
    rw [e]
    exact differentiable_const _

theorem isOsgood_comp_natAdd_dev {n m : ℕ} {K : (Fin m → ℂ) → ℂ} (hK : IsOsgood K) :
    IsOsgood fun u : Fin (n + m) → ℂ => K fun k => u (Fin.natAdd n k) := by
  refine ⟨hK.1.comp (continuous_pi fun k => continuous_apply _), fun u i => ?_⟩
  induction i using Fin.addCases with
  | left a =>
    have e : (fun z => K fun k' => Function.update u (Fin.castAdd m a) z (Fin.natAdd n k')) =
        fun _ => K fun k' => u (Fin.natAdd n k') := by
      funext z
      rw [natAdd_update_castAdd_dev]
    rw [e]
    exact differentiable_const _
  | right k =>
    have e : (fun z => K fun k' => Function.update u (Fin.natAdd n k) z (Fin.natAdd n k')) =
        fun z => K (Function.update (fun k' => u (Fin.natAdd n k')) k z) := by
      funext z
      rw [natAdd_update_dev]
    rw [e]
    exact hK.2 _ k

/-- Order `≥ 3` along `u_s − u_t ∈ Λ_u` for `f = ϑ₁(u_s − u_t)² Q`, `f` antisymmetric in `s, t` with the multipliers
of `Θ_L[0,0]` in `u_s`. -/
theorem vanishes3_core_dev (τ : ℍ) {N L : ℕ} {f Q : (Fin N → ℂ) → ℂ} (hQ : IsOsgood Q) {s t : Fin N}
    (hst : s ≠ t) (hfQ : ∀ u, f u = theta1 (u s - u t) τ ^ 2 * Q u)
    (hanti : ∀ u, f (u ∘ Equiv.swap s t) = -f u)
    (hmem : ∀ u, (fun z => f (Function.update u s z)) ∈ thetaSpace τ 0 0 L) :
    VanishesAlong τ f s t 3 := by
  -- `Q` is antisymmetric under the swap of `s, t`, so it vanishes on `u_s = u_t`
  have hQanti : ∀ u, Q (u ∘ Equiv.swap s t) = -Q u := by
    have h := eq_zero_of_offDiff_dev τ hst (φ := fun u => Q (u ∘ Equiv.swap s t) + Q u)
      ((hQ.1.comp (continuous_pi fun i => continuous_apply _)).add hQ.1) fun u hu => by
        have hθ : theta1 (u s - u t) τ ≠ 0 := fun h0 => hu ((theta1_eq_zero_iff τ _).1 h0)
        have h1 := hanti u
        rw [hfQ, hfQ] at h1
        simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at h1
        have e := theta1_sq_neg_dev (u s - u t) τ
        rw [neg_sub] at e
        rw [e] at h1
        have h2 : theta1 (u s - u t) τ ^ 2 * (Q (u ∘ Equiv.swap s t) + Q u) = 0 := by linear_combination h1
        exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero 2 hθ)
    intro u
    have := congrFun h u
    simp only [Pi.zero_apply] at this
    linear_combination this
  have hQdiag : ∀ u, u s = u t → Q u = 0 := by
    intro u hu
    have hfix : u ∘ Equiv.swap s t = u := by
      funext i
      simp only [Function.comp_apply]
      rcases eq_or_ne i s with rfl | his
      · rw [Equiv.swap_apply_left, hu]
      · rcases eq_or_ne i t with rfl | hit
        · rw [Equiv.swap_apply_right, hu]
        · rw [Equiv.swap_apply_of_ne_of_ne his hit]
    have h := hQanti u
    rw [hfix] at h
    linear_combination h / 2
  intro u l hl j hj
  set C : ℂ → ℂ := fun z => Q (Function.update u s z) with hCdef
  have hCd : Differentiable ℂ C := hQ.2 u s
  have hft : ∀ z, f (Function.update u s z) = theta1 (z - u t) τ ^ 2 * C z := by
    intro z
    rw [hfQ, Function.update_self, Function.update_of_ne hst.symm]
  have hS : ((fun l' => u t + l') '' Λu τ).Countable := (Λu_countable_dev τ).image _
  have hθne : ∀ z, z ∉ (fun l' => u t + l') '' Λu τ → theta1 (z - u t) τ ≠ 0 := fun z hz h0 =>
    hz ⟨z - u t, (theta1_eq_zero_iff τ _).1 h0, by simp⟩
  -- the multipliers of `C`
  have hC1 : ∀ z, C (z + 1) = C z := by
    have h := Continuous.ext_on (hS.dense_compl ℂ) (hCd.continuous.comp (by fun_prop : Continuous fun z : ℂ => z + 1))
      hCd.continuous fun z hz => by
        have h1 := (hmem u).2.1 z
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h1
        rw [hft, hft, show z + 1 - u t = (z - u t) + 1 by ring, theta1_add_one, neg_sq] at h1
        exact mul_left_cancel₀ (pow_ne_zero 2 (hθne z hz)) h1
    exact fun z => congrFun h z
  have hCτ : ∀ z, cexp (-2 * π * I * τ - 4 * π * I * (z - u t)) * C (z + τ) =
      cexp (-π * I * (L : ℂ) * (2 * z + τ)) * C z := by
    have h := Continuous.ext_on (hS.dense_compl ℂ)
      ((by fun_prop : Continuous fun z : ℂ => cexp (-2 * π * I * τ - 4 * π * I * (z - u t))).mul
        (hCd.continuous.comp (by fun_prop : Continuous fun z : ℂ => z + (τ : ℂ))))
      ((by fun_prop : Continuous fun z : ℂ => cexp (-π * I * (L : ℂ) * (2 * z + τ))).mul hCd.continuous)
      fun z hz => by
        have h1 := (hmem u).2.2 z
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h1
        rw [hft, hft, show z + (τ : ℂ) - u t = (z - u t) + τ by ring, theta1_add_tau] at h1
        have e2 : cexp (-π * I * τ - 2 * π * I * (z - u t)) ^ 2 =
            cexp (-2 * π * I * τ - 4 * π * I * (z - u t)) := by
          rw [← Complex.exp_nat_mul]
          congr 1
          push_cast
          ring
        have h2 : theta1 (z - u t) τ ^ 2 * (cexp (-2 * π * I * τ - 4 * π * I * (z - u t)) * C (z + τ)) =
            theta1 (z - u t) τ ^ 2 * (cexp (-π * I * (L : ℂ) * (2 * z + τ)) * C z) := by
          linear_combination h1 - (theta1 (z - u t) τ ^ 2 * C (z + τ)) * e2
        exact mul_left_cancel₀ (pow_ne_zero 2 (hθne z hz)) h2
    exact fun z => congrFun h z
  -- the zeros of `C` are invariant under the lattice
  have hZ1 : ∀ z, C z = 0 ↔ C (z + 1) = 0 := fun z => by rw [hC1]
  have hZτ : ∀ z, C z = 0 ↔ C (z + τ) = 0 := fun z => by
    constructor
    · intro h0
      have h1 := hCτ z
      rw [h0, mul_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_left (Complex.exp_ne_zero _)
    · intro h0
      have h1 := hCτ z
      rw [h0, mul_zero] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left (Complex.exp_ne_zero _)
  have h0 : C (u t) = 0 := hQdiag _ (by rw [Function.update_self, Function.update_of_ne hst.symm])
  have hq : ∀ q : ℤ, C (u t + q * τ) = 0 := by
    intro q
    induction q with
    | zero => simpa using h0
    | succ i ih =>
      have h1 := (hZτ _).1 ih
      convert h1 using 2
      push_cast
      ring
    | pred i ih =>
      refine (hZτ _).2 ?_
      convert ih using 2
      push_cast
      ring
  have hpq : ∀ p q : ℤ, C (u t + (p + q * τ)) = 0 := by
    intro p q
    induction p with
    | zero => simpa using hq q
    | succ i ih =>
      have h1 := (hZ1 _).1 ih
      convert h1 using 2
      push_cast
      ring
    | pred i ih =>
      refine (hZ1 _).2 ?_
      convert ih using 2
      push_cast
      ring
  -- the product `ϑ₁(z − u_t) · ϑ₁(z − u_t) · C(z)`
  obtain ⟨p, q, rfl⟩ := hl
  have hfun : (fun z => f (Function.update u s z)) = fun z => theta1 (z - u t) τ * theta1 (z - u t) τ * C z := by
    funext z
    rw [hft]
    ring
  have hθd : Differentiable ℂ fun z => theta1 (z - u t) τ :=
    (theta1_differentiable τ).comp (differentiable_id.sub_const _)
  have hθ0 : theta1 (u t + (p + q * τ) - u t) τ = 0 :=
    (theta1_eq_zero_iff τ _).2 ⟨p, q, by ring⟩
  rw [hfun]
  exact iteratedDeriv_mul3_dev hθd hθd hCd hθ0 hθ0 (hpq p q) j hj

/-- (C1) for a function of the shape that is `J(x)² J(y)² R` with `R` in the Osgood class. -/
theorem C1_of_factor_dev (τ : ℍ) {n m L : ℕ} {f R : (Fin (n + m) → ℂ) → ℂ} (hshape : IsCanonShape τ L n m f)
    (hR : IsOsgood R)
    (hfac : ∀ u, f u = Jfun τ (fun a => u (Fin.castAdd m a)) ^ 2 * Jfun τ (fun k => u (Fin.natAdd n k)) ^ 2 * R u) :
    C1 τ n m f := by
  intro s t hst hss
  have hne : s ≠ t := ne_of_lt hst
  have hJy : IsOsgood fun u : Fin (n + m) → ℂ => Jfun τ (fun k => u (Fin.natAdd n k)) ^ 2 :=
    isOsgood_of_differentiable_dev ((differentiable_Jfun_comp_dev τ _).pow 2)
  have hJx : IsOsgood fun u : Fin (n + m) → ℂ => Jfun τ (fun a => u (Fin.castAdd m a)) ^ 2 :=
    isOsgood_of_differentiable_dev ((differentiable_Jfun_comp_dev τ _).pow 2)
  induction s using Fin.addCases with
  | left a =>
    induction t using Fin.addCases with
    | left b =>
      have hab : a ≠ b := fun h => hne (by rw [h])
      obtain ⟨K, hK, hJ⟩ := Jfun_sq_factor τ hab
      refine vanishes3_core_dev τ (L := L) (Q := fun u => K (fun a => u (Fin.castAdd m a)) *
          Jfun τ (fun k => u (Fin.natAdd n k)) ^ 2 * R u)
        (isOsgood_mul_dev (isOsgood_mul_dev (isOsgood_comp_castAdd_dev hK) hJy) hR) hne (fun u => ?_)
        (hshape.2.2 _ _ hne hss) (fun u => hshape.2.1 u _)
      rw [hfac, hJ (fun a => u (Fin.castAdd m a))]
      ring
    | right l =>
      have hss' : ((Fin.castAdd m a : Fin (n + m)) : ℕ) < n ↔ ((Fin.natAdd n l : Fin (n + m)) : ℕ) < n := hss
      simp only [Fin.val_castAdd, Fin.val_natAdd, a.isLt, true_iff] at hss'
      omega
  | right k =>
    induction t using Fin.addCases with
    | left b =>
      have hss' : ((Fin.natAdd n k : Fin (n + m)) : ℕ) < n ↔ ((Fin.castAdd m b : Fin (n + m)) : ℕ) < n := hss
      simp only [Fin.val_castAdd, Fin.val_natAdd, b.isLt, iff_true] at hss'
      omega
    | right l =>
      have hkl : k ≠ l := fun h => hne (by rw [h])
      obtain ⟨K, hK, hJ⟩ := Jfun_sq_factor τ hkl
      refine vanishes3_core_dev τ (L := L) (Q := fun u => Jfun τ (fun a => u (Fin.castAdd m a)) ^ 2 *
          K (fun k => u (Fin.natAdd n k)) * R u)
        (isOsgood_mul_dev (isOsgood_mul_dev hJx (isOsgood_comp_natAdd_dev hK)) hR) hne (fun u => ?_)
        (hshape.2.2 _ _ hne hss) (fun u => hshape.2.1 u _)
      rw [hfac, hJ (fun k => u (Fin.natAdd n k))]
      ring

/-- Two numerators of the same state agree (continuity across the polar set). -/
theorem numerator_unique_dev (τ : ℍ) {n m : ℕ} {F : ℂ → ℂ} {g : (Fin n → ℂ) → (Fin m → ℂ) → ℂ}
    {f f' : (Fin (n + m) → ℂ) → ℂ} (hf : IsNumerator τ n m F g f) (hf' : IsNumerator τ n m F g f') : f = f' := by
  have h := eq_zero_of_offPolar_dev τ (φ := fun u => f u - f' u) (hf.1.1.sub hf'.1.1) fun u hu => by
    rw [hf.2 u hu, hf'.2 u hu, sub_self]
  funext u
  have := congrFun h u
  simp only [Pi.zero_apply] at this
  linear_combination this

/-! The explicit numerators, `F(U) J(x)² J(y)²` times a determinant built from the regularized entries. -/

/-- The determinant part of the explicit numerator of `F(U) J² g_{2m+1}`. -/
def detGOdd_dev (τ : ℍ) (m : ℕ) (u : Fin ((m + 1) + m) → ℂ) : ℂ :=
  (Matrix.of fun (a k : Fin (m + 1)) => Fin.lastCases
    (rowTheta_dev τ (fun a => u (Fin.castAdd m a)) (fun k => u (Fin.natAdd (m + 1) k)) a)
    (fun k' => regEntry_dev τ .pp (fun a => u (Fin.castAdd m a)) (fun k => u (Fin.natAdd (m + 1) k)) a k') k).det

theorem differentiable_detGOdd_dev (τ : ℍ) (m : ℕ) : Differentiable ℂ (detGOdd_dev τ m) := by
  show Differentiable ℂ fun u => detGOdd_dev τ m u
  unfold detGOdd_dev
  refine differentiable_det_dev _ fun a k => ?_
  refine Fin.lastCases ?_ (fun k' => ?_) k
  · simp only [Fin.lastCases_last]
    exact differentiable_rowTheta_dev τ _ _ a
  · simp only [Fin.lastCases_castSucc]
    exact differentiable_regEntry_dev τ .pp _ _ a k'

theorem gOdd_numerator_factor_dev (τ : ℍ) (m : ℕ) {F : ℂ → ℂ} (hF : F ∈ Θ2 τ .pp) :
    ∃ f R : (Fin ((m + 1) + m) → ℂ) → ℂ, IsNumerator τ (m + 1) m F (gOdd τ m) f ∧ Differentiable ℂ R ∧
      ∀ u, f u = Jfun τ (fun a => u (Fin.castAdd m a)) ^ 2 * Jfun τ (fun k => u (Fin.natAdd (m + 1) k)) ^ 2 * R u := by
  refine ⟨fun u => F (∑ i, u i) * Jfun τ (fun a => u (Fin.castAdd m a)) ^ 2 *
      Jfun τ (fun k => u (Fin.natAdd (m + 1) k)) ^ 2 * detGOdd_dev τ m u,
    fun u => F (∑ i, u i) * detGOdd_dev τ m u, ⟨isOsgood_of_differentiable_dev ?_, fun u hu => ?_⟩,
    (differentiable_F_sum_dev hF.1).mul (differentiable_detGOdd_dev τ m),
    fun u => by beta_reduce; ring⟩
  · exact (((differentiable_F_sum_dev hF.1).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul
      ((differentiable_Jfun_comp_dev τ _).pow 2)).mul (differentiable_detGOdd_dev τ m)
  · have hgen : ∀ a k, u (Fin.castAdd m a) - u (Fin.natAdd (m + 1) k) ∉ Λu τ := fun a k hmem => hu ⟨a, k, hmem⟩
    beta_reduce
    rw [stateFun_eq_dev, gOdd_eq_updateCol_dev τ m _ _ 0]
    congr 1
    unfold detGOdd_dev
    rw [← Matrix.det_mul_column]
    refine congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ => M.det) ?_
    ext a k
    simp only [Matrix.of_apply, Matrix.updateCol_apply]
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · simp
    · have hk : (Fin.castSucc k' : Fin (m + 1)) ≠ Fin.last m := (Fin.castSucc_lt_last k').ne
      simp only [Fin.lastCases_castSucc, hk, ite_false, Fin.snoc_castSucc]
      exact regEntry_eq_dev τ .pp _ _ a k' (hgen a k')

/-- The determinant part of the explicit numerator of `F(U) J² g_{2m+1}(y; x)`. -/
def detGOddSwap_dev (τ : ℍ) (m : ℕ) (u : Fin (m + (m + 1)) → ℂ) : ℂ :=
  (Matrix.of fun (a k : Fin (m + 1)) => Fin.lastCases
    (rowTheta_dev τ (fun k => u (Fin.natAdd m k)) (fun a => u (Fin.castAdd (m + 1) a)) a)
    (fun k' => regEntry_dev τ .pp (fun k => u (Fin.natAdd m k)) (fun a => u (Fin.castAdd (m + 1) a)) a k') k).det

theorem differentiable_detGOddSwap_dev (τ : ℍ) (m : ℕ) : Differentiable ℂ (detGOddSwap_dev τ m) := by
  show Differentiable ℂ fun u => detGOddSwap_dev τ m u
  unfold detGOddSwap_dev
  refine differentiable_det_dev _ fun a k => ?_
  refine Fin.lastCases ?_ (fun k' => ?_) k
  · simp only [Fin.lastCases_last]
    exact differentiable_rowTheta_dev τ _ _ a
  · simp only [Fin.lastCases_castSucc]
    exact differentiable_regEntry_dev τ .pp _ _ a k'

theorem gOddSwap_numerator_factor_dev (τ : ℍ) (m : ℕ) {F : ℂ → ℂ} (hF : F ∈ Θ2 τ .pp) :
    ∃ f R : (Fin (m + (m + 1)) → ℂ) → ℂ, IsNumerator τ m (m + 1) F (gOddSwap τ m) f ∧ Differentiable ℂ R ∧
      ∀ u, f u = Jfun τ (fun a => u (Fin.castAdd (m + 1) a)) ^ 2 * Jfun τ (fun k => u (Fin.natAdd m k)) ^ 2 * R u := by
  refine ⟨fun u => F (∑ i, u i) * Jfun τ (fun a => u (Fin.castAdd (m + 1) a)) ^ 2 *
      Jfun τ (fun k => u (Fin.natAdd m k)) ^ 2 * detGOddSwap_dev τ m u,
    fun u => F (∑ i, u i) * detGOddSwap_dev τ m u, ⟨isOsgood_of_differentiable_dev ?_, fun u hu => ?_⟩,
    (differentiable_F_sum_dev hF.1).mul (differentiable_detGOddSwap_dev τ m),
    fun u => by beta_reduce; ring⟩
  · exact (((differentiable_F_sum_dev hF.1).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul
      ((differentiable_Jfun_comp_dev τ _).pow 2)).mul (differentiable_detGOddSwap_dev τ m)
  · have hgen : ∀ (a : Fin (m + 1)) (k : Fin m), u (Fin.natAdd m a) - u (Fin.castAdd (m + 1) k) ∉ Λu τ := by
      intro a k hmem
      refine hu ⟨k, a, ?_⟩
      have := neg_mem_Λu_dev τ hmem
      rwa [neg_sub] at this
    beta_reduce
    rw [stateFun_eq_dev, prod_rowTheta_swap_dev]
    unfold gOddSwap
    rw [gOdd_eq_updateCol_dev τ m _ _ 0]
    congr 1
    unfold detGOddSwap_dev
    rw [← Matrix.det_mul_column]
    refine congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ => M.det) ?_
    ext a k
    simp only [Matrix.of_apply, Matrix.updateCol_apply]
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · simp
    · have hk : (Fin.castSucc k' : Fin (m + 1)) ≠ Fin.last m := (Fin.castSucc_lt_last k').ne
      simp only [Fin.lastCases_castSucc, hk, ite_false, Fin.snoc_castSucc]
      exact regEntry_eq_dev τ .pp _ _ a k' (hgen a k')

/-- The determinant part of the explicit numerator of `F(U) J² d^{(p)}_ε`. -/
def detDEps_dev (τ : ℍ) (ε : Eps) (p : ℕ) (u : Fin (p + p) → ℂ) : ℂ :=
  (Matrix.of fun a k => regEntry_dev τ ε (fun a => u (Fin.castAdd p a)) (fun k => u (Fin.natAdd p k)) a k).det

theorem differentiable_detDEps_dev (τ : ℍ) (ε : Eps) (p : ℕ) : Differentiable ℂ (detDEps_dev τ ε p) := by
  show Differentiable ℂ fun u => detDEps_dev τ ε p u
  unfold detDEps_dev
  exact differentiable_det_dev _ fun a k => differentiable_regEntry_dev τ ε _ _ a k

theorem dEps_numerator_factor_dev (τ : ℍ) (ε : Eps) (p : ℕ) {F : ℂ → ℂ} (hF : F ∈ Θ2 τ ε) :
    ∃ f R : (Fin (p + p) → ℂ) → ℂ, IsNumerator τ p p F (dEps τ ε p) f ∧ Differentiable ℂ R ∧
      ∀ u, f u = Jfun τ (fun a => u (Fin.castAdd p a)) ^ 2 * Jfun τ (fun k => u (Fin.natAdd p k)) ^ 2 * R u := by
  refine ⟨fun u => F (∑ i, u i) * Jfun τ (fun a => u (Fin.castAdd p a)) ^ 2 *
      Jfun τ (fun k => u (Fin.natAdd p k)) ^ 2 * detDEps_dev τ ε p u,
    fun u => F (∑ i, u i) * detDEps_dev τ ε p u, ⟨isOsgood_of_differentiable_dev ?_, fun u hu => ?_⟩,
    (differentiable_F_sum_dev hF.1).mul (differentiable_detDEps_dev τ ε p),
    fun u => by beta_reduce; ring⟩
  · exact (((differentiable_F_sum_dev hF.1).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul
      ((differentiable_Jfun_comp_dev τ _).pow 2)).mul (differentiable_detDEps_dev τ ε p)
  · have hgen : ∀ a k, u (Fin.castAdd p a) - u (Fin.natAdd p k) ∉ Λu τ := fun a k hmem => hu ⟨a, k, hmem⟩
    beta_reduce
    rw [stateFun_eq_dev]
    congr 1
    unfold dEps detDEps_dev
    rw [← Matrix.det_mul_column]
    refine congrArg (fun M : Matrix (Fin p) (Fin p) ℂ => M.det) ?_
    ext a k
    simp only [Matrix.of_apply]
    exact regEntry_eq_dev τ ε _ _ a k (hgen a k)

/-- The determinant part of the explicit numerator of `F(U) J² f_5^{(p)}`. -/
def detF5_dev (τ : ℍ) (q : ℕ) (u : Fin ((q + 1) + (q + 1)) → ℂ) : ℂ :=
  ∑ j, (Matrix.of fun a k => if k = j then
      rowTheta_dev τ (fun a => u (Fin.castAdd (q + 1) a)) (fun k => u (Fin.natAdd (q + 1) k)) a
    else regEntry_dev τ .pp (fun a => u (Fin.castAdd (q + 1) a)) (fun k => u (Fin.natAdd (q + 1) k)) a k).det

theorem differentiable_detF5_dev (τ : ℍ) (q : ℕ) : Differentiable ℂ (detF5_dev τ q) := by
  show Differentiable ℂ fun u => detF5_dev τ q u
  unfold detF5_dev
  exact Differentiable.fun_sum fun j _ => differentiable_det_dev _ fun a k =>
    differentiable_ite_dev _ (differentiable_rowTheta_dev τ _ _ a) (differentiable_regEntry_dev τ .pp _ _ a k)

theorem f5_numerator_factor_dev (τ : ℍ) (q : ℕ) {F : ℂ → ℂ} (hF : F ∈ Θ2 τ .pp) :
    ∃ f R : (Fin ((q + 1) + (q + 1)) → ℂ) → ℂ, IsNumerator τ (q + 1) (q + 1) F (f5 τ q) f ∧ Differentiable ℂ R ∧
      ∀ u, f u = Jfun τ (fun a => u (Fin.castAdd (q + 1) a)) ^ 2 *
        Jfun τ (fun k => u (Fin.natAdd (q + 1) k)) ^ 2 * R u := by
  refine ⟨fun u => F (∑ i, u i) * Jfun τ (fun a => u (Fin.castAdd (q + 1) a)) ^ 2 *
      Jfun τ (fun k => u (Fin.natAdd (q + 1) k)) ^ 2 * detF5_dev τ q u,
    fun u => F (∑ i, u i) * detF5_dev τ q u, ⟨isOsgood_of_differentiable_dev ?_, fun u hu => ?_⟩,
    (differentiable_F_sum_dev hF.1).mul (differentiable_detF5_dev τ q),
    fun u => by beta_reduce; ring⟩
  · exact (((differentiable_F_sum_dev hF.1).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul
      ((differentiable_Jfun_comp_dev τ _).pow 2)).mul (differentiable_detF5_dev τ q)
  · have hgen : ∀ a k, u (Fin.castAdd (q + 1) a) - u (Fin.natAdd (q + 1) k) ∉ Λu τ :=
      fun a k hmem => hu ⟨a, k, hmem⟩
    beta_reduce
    rw [stateFun_eq_dev, f5_eq_sum_dev]
    congr 1
    unfold detF5_dev
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Matrix.det_mul_column]
    congr 1
    ext a k
    simp only [Matrix.of_apply, Matrix.updateCol_apply]
    split_ifs with hk
    · ring
    · exact regEntry_eq_dev τ .pp _ _ a k (hgen a k)

/-! ### Proof devices for (C2) (proof phase, round two; not statements of the paper)

The paper's argument: "`(C2): apply Lemma~\ref{kz:lem:even} with`" `S` symmetric, the `v⁻¹` coefficient of `g` being
zero because "`(v): the coefficient of the entry $\wp_\varepsilon(x_i-y_j)$ in the determinant (its cofactor) depends on neither $x_i$ nor $y_j$, and the remaining terms are regular at generic points of $x_i=y_j$.`"
Here: at a point of `x_a = y_k` where every other up–down pair is off the lattice, `g` along the merge
`x_a = w + v/2`, `y_k = w − v/2` is `c ℘_ε(v) + H(v)` with `c` the cofactor and `H` analytic at `0`
(`det_entry_affine_dev`, `det_laurent_dev`, `*_laurent_dev`); `J² = ϑ₁(v)² K` with `K` symmetric under the exchange,
so Lemma C.even gives the derivative zero there; every point of `x_a = y_k` is a limit of such points along a complex
line inside `x_a = y_k`, and the derivative at `v = 0` is continuous along it (F0's `D1_continuous_dev`, the numerator
being differentiable) (`C2_of_laurent_dev`). -/

theorem analyticAt_fun_sum_dev {α : Type*} (N : Finset α) {f : α → ℂ → ℂ} {z : ℂ}
    (h : ∀ i ∈ N, AnalyticAt ℂ (f i) z) : AnalyticAt ℂ (fun v => ∑ i ∈ N, f i v) z := by
  have e : (fun v => ∑ i ∈ N, f i v) = ∑ i ∈ N, f i := by
    funext v
    rw [Finset.sum_apply]
  rw [e]
  exact Finset.analyticAt_sum N h

theorem analyticAt_det_dev {q : ℕ} (N : ℂ → Matrix (Fin q) (Fin q) ℂ) {z : ℂ}
    (hN : ∀ i j, AnalyticAt ℂ (fun v => N v i j) z) : AnalyticAt ℂ (fun v => (N v).det) z := by
  have e : (fun v => (N v).det) = fun v => ∑ σ : Equiv.Perm (Fin q),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, N v (σ i) i := by
    funext v
    rw [Matrix.det_apply']
  rw [e]
  exact analyticAt_fun_sum_dev _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hN (σ i) i)

/-- The determinant is affine in each entry, the coefficient being the cofactor. -/
theorem det_entry_affine_dev {q : ℕ} (M : Matrix (Fin (q + 1)) (Fin (q + 1)) ℂ) (a k : Fin (q + 1)) :
    M.det = M a k * ((-1) ^ ((a : ℕ) + (k : ℕ)) * (M.submatrix a.succAbove k.succAbove).det) +
      (M.updateRow a (Function.update (M a) k 0)).det := by
  have hrow : M a = M a k • Pi.single k 1 + Function.update (M a) k 0 := by
    funext j
    by_cases hj : j = k
    · rw [hj]
      simp
    · simp [hj]
  conv_lhs => rw [← Matrix.updateRow_eq_self M a, hrow]
  rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul, ← Matrix.adjugate_apply,
    Matrix.adjugate_fin_succ_eq_det_submatrix]

/-- A determinant one entry of which is `φ(v)`, the others analytic at `0`, and the entries off that row and column
constant, is `c φ(v) + H(v)` with `H` analytic at `0`. -/
theorem det_laurent_dev {q : ℕ} (N : ℂ → Matrix (Fin (q + 1)) (Fin (q + 1)) ℂ) (a k : Fin (q + 1)) {φ : ℂ → ℂ}
    (hak : ∀ v, N v a k = φ v) (han : ∀ i j, (i ≠ a ∨ j ≠ k) → AnalyticAt ℂ (fun v => N v i j) 0)
    (hconst : ∀ i j, i ≠ a → j ≠ k → ∀ v, N v i j = N 0 i j) :
    ∃ c : ℂ, ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ ∀ v, (N v).det = c * φ v + H v := by
  refine ⟨(-1) ^ ((a : ℕ) + (k : ℕ)) * ((N 0).submatrix a.succAbove k.succAbove).det,
    fun v => ((N v).updateRow a (Function.update (N v a) k 0)).det, ?_, fun v => ?_⟩
  · refine analyticAt_det_dev _ fun i j => ?_
    by_cases hi : i = a
    · rw [hi]
      by_cases hj : j = k
      · rw [hj]
        simp only [Matrix.updateRow_self, Function.update_self]
        exact analyticAt_const
      · simp only [Matrix.updateRow_self, Function.update_of_ne hj]
        exact han a j (Or.inr hj)
    · simp only [Matrix.updateRow_ne hi]
      exact han i j (Or.inl hi)
  · have h2 : (N v).submatrix a.succAbove k.succAbove = (N 0).submatrix a.succAbove k.succAbove := by
      ext i' j'
      exact hconst _ _ (Fin.succAbove_ne a i') (Fin.succAbove_ne k j') v
    rw [det_entry_affine_dev (N v) a k, hak, h2]
    ring

/-- The matrix `[℘_ε(x_i − y_j)]` along the merge `x_a = x_a + v/2`, `y_k = y_k − v/2`. -/
def mergeMat_dev (τ : ℍ) (ε : Eps) {q : ℕ} (a k : Fin (q + 1)) (x y : Fin (q + 1) → ℂ) (v : ℂ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℂ :=
  Matrix.of fun i j => wpE τ ε (Function.update x a (x a + v / 2) i - Function.update y k (y k - v / 2) j)

theorem mergeMat_ak_dev (τ : ℍ) (ε : Eps) {q : ℕ} (a k : Fin (q + 1)) (x y : Fin (q + 1) → ℂ) (hxy : x a = y k)
    (v : ℂ) : mergeMat_dev τ ε a k x y v a k = wpE τ ε v := by
  simp only [mergeMat_dev, Matrix.of_apply, Function.update_self]
  rw [hxy]
  congr 1
  ring

theorem mergeMat_analyticAt_dev (τ : ℍ) (ε : Eps) {q : ℕ} (a k : Fin (q + 1)) (x y : Fin (q + 1) → ℂ)
    (hgen : ∀ a' k', (a' ≠ a ∨ k' ≠ k) → x a' - y k' ∉ Λu τ) (i j : Fin (q + 1)) (hij : i ≠ a ∨ j ≠ k) :
    AnalyticAt ℂ (fun v => mergeMat_dev τ ε a k x y v i j) 0 := by
  simp only [mergeMat_dev, Matrix.of_apply]
  by_cases hi : i = a
  · have hj : j ≠ k := hij.resolve_left (not_not.2 hi)
    rw [hi]
    simp only [Function.update_self, Function.update_of_ne hj]
    exact (wpE_analyticAt τ ε (hgen a j (Or.inr hj))).comp_of_eq (by fun_prop) (by simp)
  · simp only [Function.update_of_ne hi]
    by_cases hj : j = k
    · rw [hj]
      simp only [Function.update_self]
      exact (wpE_analyticAt τ ε (hgen i k (Or.inl hi))).comp_of_eq (by fun_prop) (by simp)
    · simp only [Function.update_of_ne hj]
      exact analyticAt_const

theorem mergeMat_const_dev (τ : ℍ) (ε : Eps) {q : ℕ} (a k : Fin (q + 1)) (x y : Fin (q + 1) → ℂ)
    (i j : Fin (q + 1)) (hi : i ≠ a) (hj : j ≠ k) (v : ℂ) :
    mergeMat_dev τ ε a k x y v i j = mergeMat_dev τ ε a k x y 0 i j := by
  simp only [mergeMat_dev, Matrix.of_apply, Function.update_of_ne hi, Function.update_of_ne hj]

theorem dEps_laurent_dev (τ : ℍ) (ε : Eps) (q : ℕ) (a k : Fin (q + 1)) (x y : Fin (q + 1) → ℂ) (hxy : x a = y k)
    (hgen : ∀ a' k', (a' ≠ a ∨ k' ≠ k) → x a' - y k' ∉ Λu τ) :
    ∃ c : ℂ, ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ ∀ v,
      dEps τ ε (q + 1) (Function.update x a (x a + v / 2)) (Function.update y k (y k - v / 2)) =
        c * wpE τ ε v + H v :=
  det_laurent_dev (mergeMat_dev τ ε a k x y) a k (mergeMat_ak_dev τ ε a k x y hxy)
    (mergeMat_analyticAt_dev τ ε a k x y hgen) (mergeMat_const_dev τ ε a k x y)

theorem f5_laurent_dev (τ : ℍ) (q : ℕ) (a k : Fin (q + 1)) (x y : Fin (q + 1) → ℂ) (hxy : x a = y k)
    (hgen : ∀ a' k', (a' ≠ a ∨ k' ≠ k) → x a' - y k' ∉ Λu τ) :
    ∃ c : ℂ, ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ ∀ v,
      f5 τ q (Function.update x a (x a + v / 2)) (Function.update y k (y k - v / 2)) = c * wp τ v + H v := by
  have hterm : ∀ j, ∃ c : ℂ, ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ ∀ v,
      ((mergeMat_dev τ .pp a k x y v).updateCol j fun _ => 1).det = c * wp τ v + H v := by
    intro j
    by_cases hjk : j = k
    · refine ⟨0, fun v => ((mergeMat_dev τ .pp a k x y v).updateCol j fun _ => 1).det,
        analyticAt_det_dev _ fun i j' => ?_, fun v => by simp⟩
      by_cases hj' : j' = j
      · rw [hj']
        simp only [Matrix.updateCol_self]
        exact analyticAt_const
      · simp only [Matrix.updateCol_ne hj']
        exact mergeMat_analyticAt_dev τ .pp a k x y hgen i j' (Or.inr (by rwa [← hjk]))
    · refine det_laurent_dev (fun v => (mergeMat_dev τ .pp a k x y v).updateCol j fun _ => 1) a k
        (fun v => ?_) (fun i j' hij => ?_) (fun i j' hi hj' v => ?_)
      · simp only [Matrix.updateCol_ne (Ne.symm hjk)]
        exact mergeMat_ak_dev τ .pp a k x y hxy v
      · by_cases hj' : j' = j
        · rw [hj']
          simp only [Matrix.updateCol_self]
          exact analyticAt_const
        · simp only [Matrix.updateCol_ne hj']
          exact mergeMat_analyticAt_dev τ .pp a k x y hgen i j' hij
      · by_cases hjj : j' = j
        · rw [hjj]
          simp only [Matrix.updateCol_self]
        · simp only [Matrix.updateCol_ne hjj]
          exact mergeMat_const_dev τ .pp a k x y i j' hi hj' v
  choose c H hH hcH using hterm
  refine ⟨∑ j, c j, fun v => ∑ j, H j v, analyticAt_fun_sum_dev _ fun j _ => hH j, fun v => ?_⟩
  rw [f5_eq_sum_dev]
  exact (Finset.sum_congr rfl fun j _ => hcH j v).trans (by rw [Finset.sum_add_distrib, Finset.sum_mul])

theorem gOdd_laurent_dev (τ : ℍ) (m : ℕ) (a : Fin (m + 1)) (k : Fin m) (x : Fin (m + 1) → ℂ) (y : Fin m → ℂ)
    (hxy : x a = y k) (hgen : ∀ a' k', (a' ≠ a ∨ k' ≠ k) → x a' - y k' ∉ Λu τ) :
    ∃ c : ℂ, ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ ∀ v,
      gOdd τ m (Function.update x a (x a + v / 2)) (Function.update y k (y k - v / 2)) = c * wp τ v + H v := by
  let N : ℂ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := fun v =>
    (Matrix.of fun (i j : Fin (m + 1)) => wp τ (Function.update x a (x a + v / 2) i -
      (Fin.snoc (Function.update y k (y k - v / 2)) 0 : Fin (m + 1) → ℂ) j)).updateCol (Fin.last m) fun _ => 1
  have hak : ∀ v, N v a (Fin.castSucc k) = wp τ v := by
    intro v
    simp only [N, Matrix.updateCol_ne (Fin.castSucc_lt_last k).ne, Matrix.of_apply, Fin.snoc_castSucc,
      Function.update_self]
    rw [hxy]
    congr 1
    ring
  have han : ∀ i j, (i ≠ a ∨ j ≠ Fin.castSucc k) → AnalyticAt ℂ (fun v => N v i j) 0 := by
    intro i j hij
    induction j using Fin.lastCases with
    | last =>
      simp only [N, Matrix.updateCol_self]
      exact analyticAt_const
    | cast j' =>
      simp only [N, Matrix.updateCol_ne (Fin.castSucc_lt_last j').ne, Matrix.of_apply, Fin.snoc_castSucc]
      by_cases hi : i = a
      · have hj : j' ≠ k := fun h => (hij.resolve_left (not_not.2 hi)) (by rw [h])
        rw [hi]
        simp only [Function.update_self, Function.update_of_ne hj]
        exact (wp_analyticAt τ (hgen a j' (Or.inr hj))).comp_of_eq (by fun_prop) (by simp)
      · simp only [Function.update_of_ne hi]
        by_cases hj : j' = k
        · rw [hj]
          simp only [Function.update_self]
          exact (wp_analyticAt τ (hgen i k (Or.inl hi))).comp_of_eq (by fun_prop) (by simp)
        · simp only [Function.update_of_ne hj]
          exact analyticAt_const
  have hconst : ∀ i j, i ≠ a → j ≠ Fin.castSucc k → ∀ v, N v i j = N 0 i j := by
    intro i j hi hj v
    induction j using Fin.lastCases with
    | last => simp only [N, Matrix.updateCol_self]
    | cast j' =>
      have hj' : j' ≠ k := fun h => hj (by rw [h])
      simp only [N, Matrix.updateCol_ne (Fin.castSucc_lt_last j').ne, Matrix.of_apply, Fin.snoc_castSucc,
        Function.update_of_ne hi, Function.update_of_ne hj']
  obtain ⟨c, H, hH, hcH⟩ := det_laurent_dev N a (Fin.castSucc k) hak han hconst
  refine ⟨c, H, hH, fun v => ?_⟩
  rw [gOdd_eq_updateCol_dev τ m _ _ 0]
  exact hcH v

theorem gOddSwap_laurent_dev (τ : ℍ) (m : ℕ) (a : Fin m) (k : Fin (m + 1)) (x : Fin m → ℂ) (y : Fin (m + 1) → ℂ)
    (hxy : x a = y k) (hgen : ∀ a' k', (a' ≠ a ∨ k' ≠ k) → x a' - y k' ∉ Λu τ) :
    ∃ c : ℂ, ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ ∀ v,
      gOddSwap τ m (Function.update x a (x a + v / 2)) (Function.update y k (y k - v / 2)) = c * wp τ v + H v := by
  obtain ⟨c, H, hH, hcH⟩ := gOdd_laurent_dev τ m k a y x hxy.symm fun k' a' hne hmem =>
    hgen a' k' hne.symm (by have h := neg_mem_Λu_dev τ hmem; rwa [neg_sub] at h)
  refine ⟨c, fun v => H (-v), hH.comp_of_eq (by fun_prop) (by simp), fun v => ?_⟩
  have h := hcH (-v)
  rw [show y k + -v / 2 = y k - v / 2 by ring, show x a - -v / 2 = x a + v / 2 by ring, wp_neg] at h
  unfold gOddSwap
  exact h

/-- A function in the Osgood class along the merge of two of its variables is differentiable. -/
theorem differentiable_osgood_merge_dev {N : ℕ} {K : (Fin N → ℂ) → ℂ} (hK : IsOsgood K) {s t : Fin N} (hst : s ≠ t)
    (u : Fin N → ℂ) :
    Differentiable ℂ fun v : ℂ => K (Function.update (Function.update u s (u s + v / 2)) t (u t - v / 2)) := by
  set G : ℂ × ℂ → ℂ := fun p => K (Function.update (Function.update u s p.1) t p.2) with hG
  have hGos : IsOsgood2_dev G := by
    refine ⟨?_, fun b => ?_, fun a => ?_⟩
    · refine hK.1.comp (continuous_pi fun i => ?_)
      by_cases hit : i = t
      · subst hit
        simp only [Function.update_self]
        exact continuous_snd
      · by_cases his : i = s
        · subst his
          simp only [Function.update_of_ne hit, Function.update_self]
          exact continuous_fst
        · simp only [Function.update_of_ne hit, Function.update_of_ne his]
          exact continuous_const
    · have e : (fun a => G (a, b)) = fun a => K (Function.update (Function.update u t b) s a) :=
        funext fun a => by simp only [hG]; rw [Function.update_comm hst]
      rw [e]
      exact hK.2 _ s
    · exact hK.2 (Function.update u s a) t
  have hpath : Differentiable ℂ fun v : ℂ => (u s + v / 2, u t - v / 2) :=
    ((differentiable_const _).add (differentiable_id.div_const 2)).prodMk
      ((differentiable_const _).sub (differentiable_id.div_const 2))
  exact (isOsgood2_differentiable_dev hGos).comp hpath

/-- (C2) for a numerator whose `g` has, along each up–down merge at generic points, the form `c φ(v) + H(v)` with
`φ − v⁻²` and `H` analytic at `0`. -/
theorem C2_of_laurent_dev (τ : ℍ) {n m : ℕ} {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {g : (Fin n → ℂ) → (Fin m → ℂ) → ℂ} {f : (Fin (n + m) → ℂ) → ℂ} (hf : IsNumerator τ n m F g f)
    (hfd : Differentiable ℂ f) {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ (fun v => φ v - 1 / v ^ 2) 0)
    (hL : ∀ (a : Fin n) (k : Fin m) (x : Fin n → ℂ) (y : Fin m → ℂ), x a = y k →
      (∀ a' k', (a' ≠ a ∨ k' ≠ k) → x a' - y k' ∉ Λu τ) →
      ∃ c : ℂ, ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ ∀ v,
        g (Function.update x a (x a + v / 2)) (Function.update y k (y k - v / 2)) = c * φ v + H v) :
    C2 n m f := by
  intro s t hs ht u0 hu0
  obtain ⟨a, rfl⟩ : ∃ a : Fin n, Fin.castAdd m a = s := ⟨⟨s, hs⟩, Fin.ext rfl⟩
  obtain ⟨k, rfl⟩ : ∃ k : Fin m, Fin.natAdd n k = t :=
    ⟨⟨(t : ℕ) - n, by have := t.isLt; omega⟩, Fin.ext (by simp only [Fin.val_natAdd]; omega)⟩
  have hst : Fin.castAdd m a ≠ Fin.natAdd n k := castAdd_ne_natAdd_dev a k
  let P : (Fin (n + m) → ℂ) → ℂ → (Fin (n + m) → ℂ) := fun u v =>
    Function.update (Function.update u (Fin.castAdd m a) (u (Fin.castAdd m a) + v / 2)) (Fin.natAdd n k)
      (u (Fin.natAdd n k) - v / 2)
  obtain ⟨K, hK, hJ⟩ := Jfun_sq_factor τ hst
  -- `K` is symmetric under the exchange of the two variables
  have hKsym : ∀ u, K (u ∘ Equiv.swap (Fin.castAdd m a) (Fin.natAdd n k)) = K u := by
    have h := eq_zero_of_offDiff_dev τ hst
      (φ := fun u => K (u ∘ Equiv.swap (Fin.castAdd m a) (Fin.natAdd n k)) - K u)
      ((hK.1.comp (continuous_pi fun i => continuous_apply _)).sub hK.1) fun u hu => by
        have hθ : theta1 (u (Fin.castAdd m a) - u (Fin.natAdd n k)) τ ≠ 0 := fun h0 =>
          hu ((theta1_eq_zero_iff τ _).1 h0)
        have h1 := Jfun_sq_perm (τ : ℂ) (Equiv.swap (Fin.castAdd m a) (Fin.natAdd n k)) u
        rw [hJ, hJ] at h1
        simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at h1
        have e := theta1_sq_neg_dev (u (Fin.castAdd m a) - u (Fin.natAdd n k)) τ
        rw [neg_sub] at e
        rw [e] at h1
        have h2 : theta1 (u (Fin.castAdd m a) - u (Fin.natAdd n k)) τ ^ 2 *
            (K (u ∘ Equiv.swap (Fin.castAdd m a) (Fin.natAdd n k)) - K u) = 0 := by linear_combination h1
        exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero 2 hθ)
    intro u
    have := congrFun h u
    simp only [Pi.zero_apply] at this
    linear_combination this
  -- the merge path and its coordinates
  have hPd : ∀ u, Differentiable ℂ fun v => P u v := by
    intro u
    refine differentiable_pi.2 fun i => ?_
    simp only [P, Function.update_apply]
    split_ifs <;> fun_prop
  have hPst : ∀ u, u (Fin.castAdd m a) = u (Fin.natAdd n k) → ∀ v,
      P u v (Fin.castAdd m a) - P u v (Fin.natAdd n k) = v := by
    intro u hu v
    simp only [P, Function.update_self, Function.update_of_ne hst]
    rw [hu]
    ring
  have hxP : ∀ u v, (fun a' => P u v (Fin.castAdd m a')) =
      Function.update (fun a' => u (Fin.castAdd m a')) a (u (Fin.castAdd m a) + v / 2) := by
    intro u v
    funext a'
    simp only [P]
    rw [Function.update_of_ne (castAdd_ne_natAdd_dev a' k)]
    exact congrFun (castAdd_update_dev u a _) a'
  have hyP : ∀ u v, (fun k' => P u v (Fin.natAdd n k')) =
      Function.update (fun k' => u (Fin.natAdd n k')) k (u (Fin.natAdd n k) - v / 2) := by
    intro u v
    funext k'
    simp only [P]
    rw [← natAdd_update_castAdd_dev u a (u (Fin.castAdd m a) + v / 2)]
    exact congrFun (natAdd_update_dev _ k _) k'
  -- (a) the derivative vanishes at the generic points of `x_a = y_k`
  have hgeneric : ∀ u : Fin (n + m) → ℂ, u (Fin.castAdd m a) = u (Fin.natAdd n k) →
      (∀ a' k', (a' ≠ a ∨ k' ≠ k) → u (Fin.castAdd m a') - u (Fin.natAdd n k') ∉ Λu τ) →
      deriv (fun v => f (P u v)) 0 = 0 := by
    intro u hu hgen
    obtain ⟨c, H, hH, hgH⟩ := hL a k (fun a' => u (Fin.castAdd m a')) (fun k' => u (Fin.natAdd n k')) hu hgen
    have hSd : Differentiable ℂ fun v => F (∑ i, P u v i) * K (P u v) :=
      ((differentiable_F_sum_dev hF).comp (hPd u)).mul (differentiable_osgood_merge_dev hK hst u)
    have hS : AnalyticAt ℂ (fun v => F (∑ i, P u v i) * K (P u v)) 0 := hSd.analyticAt 0
    have hPswap : ∀ v, P u (-v) = P u v ∘ Equiv.swap (Fin.castAdd m a) (Fin.natAdd n k) := by
      intro v
      funext i
      simp only [P, Function.comp_apply]
      rcases eq_or_ne i (Fin.castAdd m a) with h | his
      · rw [h, Equiv.swap_apply_left, Function.update_of_ne hst, Function.update_self, Function.update_self, hu]
        ring
      · rcases eq_or_ne i (Fin.natAdd n k) with h | hit
        · rw [h, Equiv.swap_apply_right, Function.update_self, Function.update_of_ne hst, Function.update_self, hu]
          ring
        · rw [Equiv.swap_apply_of_ne_of_ne his hit, Function.update_of_ne hit, Function.update_of_ne his,
            Function.update_of_ne hit, Function.update_of_ne his]
    have hSe : ∀ v, F (∑ i, P u (-v) i) * K (P u (-v)) = F (∑ i, P u v i) * K (P u v) := by
      intro v
      rw [hPswap v, hKsym]
      simp only [Function.comp_apply]
      rw [Equiv.sum_comp]
    have hg : AnalyticAt ℂ (fun v => g (fun a' => P u v (Fin.castAdd m a')) (fun k' => P u v (Fin.natAdd n k')) -
        c / v ^ 2 - 0 / v) 0 := by
      have e : (fun v => g (fun a' => P u v (Fin.castAdd m a')) (fun k' => P u v (Fin.natAdd n k')) -
          c / v ^ 2 - 0 / v) = fun v => c * (φ v - 1 / v ^ 2) + H v := by
        funext v
        rw [hxP u v, hyP u v, hgH v]
        ring
      rw [e]
      exact (analyticAt_const.mul hφ).add hH
    obtain ⟨h, hh, hhe, hhd⟩ := lemEven τ (S := fun v => F (∑ i, P u v i) * K (P u v)) hS hSe hg
    -- off the polar set near `v = 0`
    have hall : ∀ᶠ v in 𝓝 (0 : ℂ), ∀ a' k', (a' ≠ a ∨ k' ≠ k) →
        P u v (Fin.castAdd m a') - P u v (Fin.natAdd n k') ∉ Λu τ := by
      have hP0 : P u 0 = u := by simp [P]
      refine Filter.eventually_all.2 fun a' => Filter.eventually_all.2 fun k' => ?_
      by_cases hne : a' ≠ a ∨ k' ≠ k
      · have hc : Continuous fun v => P u v (Fin.castAdd m a') - P u v (Fin.natAdd n k') :=
          ((continuous_apply (Fin.castAdd m a')).comp (hPd u).continuous).sub
            ((continuous_apply (Fin.natAdd n k')).comp (hPd u).continuous)
        have h0 := (hc.tendsto 0).eventually (by simp only [hP0]; exact not_mem_Λu_nhds_dev τ (hgen a' k' hne))
        exact h0.mono fun v hv _ => hv
      · exact Filter.Eventually.of_forall fun v h' => absurd h' hne
    have hpolev : ∀ᶠ v in 𝓝[≠] (0 : ℂ), P u v ∉ polarSet τ n m := by
      filter_upwards [not_mem_Λu_punctured_dev τ (zero_mem_Λu_dev τ), nhdsWithin_le_nhds hall] with v hv hv2
      rintro ⟨a', k', hmem⟩
      by_cases hne : a' ≠ a ∨ k' ≠ k
      · exact hv2 a' k' hne hmem
      · obtain ⟨h1, h2⟩ := not_or.1 hne
        rw [not_not.1 h1, not_not.1 h2, hPst u hu v] at hmem
        exact hv hmem
    have hev : ∀ᶠ v in 𝓝[≠] (0 : ℂ), f (P u v) = h v := by
      filter_upwards [hhe, hpolev] with v hv hpol
      rw [hv, hf.2 _ hpol]
      unfold stateFun
      rw [hJ (P u v), hPst u hu v]
      ring
    have hcont0 : ContinuousAt (fun v => f (P u v)) 0 := (hf.1.1.comp (hPd u).continuous).continuousAt
    have heq0 : f (P u 0) = h 0 := by
      have t1 : Tendsto (fun v => f (P u v)) (𝓝[≠] 0) (𝓝 (f (P u 0))) :=
        hcont0.tendsto.mono_left nhdsWithin_le_nhds
      have t2 : Tendsto h (𝓝[≠] 0) (𝓝 (h 0)) := hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique (t1.congr' hev) t2
    have hevn : (fun v => f (P u v)) =ᶠ[𝓝 (0 : ℂ)] h := by
      have h' := hev
      rw [eventually_nhdsWithin_iff] at h'
      filter_upwards [h'] with v hv
      by_cases hv0 : v = 0
      · rw [hv0]
        exact heq0
      · exact hv hv0
    rw [hevn.deriv_eq, hhd, mul_zero]
  -- (b) along a complex line inside `x_a = y_k` the generic points are dense, and the derivative is continuous
  let δ : Fin (n + m) → ℂ := fun i =>
    if i = Fin.natAdd n k then ((Fin.castAdd m a : Fin (n + m)) : ℕ) else ((i : ℕ) : ℂ)
  let ℓ : ℂ → Fin (n + m) → ℂ := fun c => u0 + c • δ
  have hℓs : ∀ c, ℓ c (Fin.castAdd m a) = ℓ c (Fin.natAdd n k) := by
    intro c
    simp [ℓ, δ, hst, hu0]
  have hδ : ∀ a' k', (a' ≠ a ∨ k' ≠ k) → δ (Fin.castAdd m a') - δ (Fin.natAdd n k') ≠ 0 := by
    intro a' k' hne h0
    rw [sub_eq_zero] at h0
    simp only [δ, castAdd_ne_natAdd_dev a' k, ite_false] at h0
    by_cases hk : k' = k
    · simp only [hk, ite_true] at h0
      have h1 : ((Fin.castAdd m a' : Fin (n + m)) : ℕ) = ((Fin.castAdd m a : Fin (n + m)) : ℕ) := by exact_mod_cast h0
      simp only [Fin.val_castAdd] at h1
      exact hne.elim (fun ha => ha (Fin.ext h1)) (fun hk' => hk' hk)
    · have hk' : Fin.natAdd n k' ≠ Fin.natAdd n k := fun h => hk (Fin.natAdd_injective m n h)
      simp only [hk', ite_false] at h0
      have h1 : ((Fin.castAdd m a' : Fin (n + m)) : ℕ) = ((Fin.natAdd n k' : Fin (n + m)) : ℕ) := by exact_mod_cast h0
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h1
      have := a'.isLt
      omega
  let B : Set ℂ := ⋃ a' : Fin n, ⋃ k' : Fin m,
    (fun l => (l - (u0 (Fin.castAdd m a') - u0 (Fin.natAdd n k'))) /
      (δ (Fin.castAdd m a') - δ (Fin.natAdd n k'))) '' Λu τ
  have hB : B.Countable :=
    Set.countable_iUnion fun a' => Set.countable_iUnion fun k' => (Λu_countable_dev τ).image _
  have hgenℓ : ∀ c ∉ B, ∀ a' k', (a' ≠ a ∨ k' ≠ k) →
      ℓ c (Fin.castAdd m a') - ℓ c (Fin.natAdd n k') ∉ Λu τ := by
    intro c hc a' k' hne hmem
    apply hc
    refine Set.mem_iUnion.2 ⟨a', Set.mem_iUnion.2 ⟨k', ⟨_, hmem, ?_⟩⟩⟩
    have hd := hδ a' k' hne
    simp only [ℓ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_eq_iff hd]
    ring
  let G : ℂ × ℂ → ℂ := fun q => f (P (ℓ q.2) q.1)
  have hGd : Differentiable ℂ G := by
    refine hfd.comp (differentiable_pi.2 fun i => ?_)
    simp only [P, ℓ, Function.update_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> fun_prop
  have hGos : IsOsgood2_dev G :=
    ⟨hGd.continuous, fun y => hGd.comp (differentiable_id.prodMk (differentiable_const y)),
      fun x => hGd.comp ((differentiable_const x).prodMk differentiable_id)⟩
  have hcont : Continuous fun c => deriv (fun v => f (P (ℓ c) v)) 0 :=
    (D1_continuous_dev hGos).comp ((continuous_const : Continuous fun _ : ℂ => (0 : ℂ)).prodMk continuous_id)
  have hΦ : (fun c => deriv (fun v => f (P (ℓ c) v)) 0) = fun _ => 0 :=
    Continuous.ext_on (hB.dense_compl ℂ) hcont continuous_const fun c hc =>
      hgeneric (ℓ c) (hℓs c) (hgenℓ c hc)
  have h0 := congrFun hΦ 0
  have hℓ0 : ℓ 0 = u0 := by simp [ℓ]
  simp only [hℓ0] at h0
  rw [relDeriv_eq_two_deriv hf.1 hst u0 hu0]
  show 2 * deriv (fun v => f (P u0 v)) 0 = 0
  rw [h0, mul_zero]

/-! ## Membership: the numerators exist, have the shape of canonical components, and satisfy (C1), (C2)

The membership half of Lemma C.B(b) for the explicit `g` of Proposition C.explicit: "`$J^2g$ has no poles along any divisor, so it is holomorphic.`";
the boundary conditions (`L = 2N`); "`(C1): $J^2$ vanishes to order $2$ on same-spin divisors and $g$ vanishes there, so $f$ vanishes to order $\ge3$.`";
"`(C2): apply Lemma~\ref{kz:lem:even} with`" `S` symmetric, the `v⁻¹` coefficient of `g` being zero because "`(v): the coefficient of the entry $\wp_\varepsilon(x_i-y_j)$ in the determinant (its cofactor) depends on neither $x_i$ nor $y_j$, and the remaining terms are regular at generic points of $x_i=y_j$.`" -/

/-- **Proposition C.explicit(a)** with **Lemma C.B(b)** ("well defined"): the numerator of `F(U) J² g_{2m+1}` exists. -/
theorem gOdd_numerator_exists (τ : ℍ) (m : ℕ) {F : ℂ → ℂ} (hF : F ∈ Θ2 τ .pp) :
    ∃ f, IsNumerator τ (m + 1) m F (gOdd τ m) f := by
  obtain ⟨f, -, hf, -⟩ := gOdd_numerator_factor_dev τ m hF
  exact ⟨f, hf⟩

/-- **Proposition C.explicit(a)** with **Lemma C.B(b)**: the numerator is a canonical-component shape at `L = 2N` and
satisfies (C1), (C2). -/
theorem gOdd_numerator_props (τ : ℍ) (m : ℕ) {F : ℂ → ℂ} (hF : F ∈ Θ2 τ .pp) {f : (Fin ((m + 1) + m) → ℂ) → ℂ}
    (hf : IsNumerator τ (m + 1) m F (gOdd τ m) f) :
    IsCanonShape τ (2 * ((m + 1) + m)) (m + 1) m f ∧ C1 τ (m + 1) m f ∧ C2 (m + 1) m f := by
  have hG := gOdd_G τ m
  have hshape := shape_of_numerator_dev τ .pp hF (gOdd τ m)
    (fun x y a => by rw [(hG.2.1 x y a).1]; simp only [Eps.e1, one_mul])
    (fun x y a => by rw [(hG.2.1 x y a).2]; simp only [Eps.e2, one_mul])
    (fun x y k => by rw [(hG.2.2.1 x y k).1]; simp only [Eps.e1, one_mul])
    (fun x y k => by rw [(hG.2.2.1 x y k).2]; simp only [Eps.e2, one_mul])
    hG.2.2.2.1 hG.2.2.2.2 hf
  obtain ⟨f₀, R, hf₀, hR, hfac⟩ := gOdd_numerator_factor_dev τ m hF
  have heq := numerator_unique_dev τ hf hf₀
  have hfd : Differentiable ℂ f := by
    rw [heq, funext hfac]
    exact (((differentiable_Jfun_comp_dev τ _).pow 2).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul hR
  exact ⟨hshape, C1_of_factor_dev τ hshape (isOsgood_of_differentiable_dev hR) fun u => by rw [heq]; exact hfac u,
    C2_of_laurent_dev τ hF.1 hf hfd (wp_sub_inv_sq_analyticAt τ) fun a k x y hxy hgen =>
      gOdd_laurent_dev τ m a k x y hxy hgen⟩

/-- **Theorem C.T2(ii)**, `S_z = −½`: the numerator of `F(U) J² g_{2m+1}(y; x)` exists. -/
theorem gOddSwap_numerator_exists (τ : ℍ) (m : ℕ) {F : ℂ → ℂ} (hF : F ∈ Θ2 τ .pp) :
    ∃ f, IsNumerator τ m (m + 1) F (gOddSwap τ m) f := by
  obtain ⟨f, -, hf, -⟩ := gOddSwap_numerator_factor_dev τ m hF
  exact ⟨f, hf⟩

/-- **Theorem C.T2(ii)**, `S_z = −½`: shape, (C1), (C2). -/
theorem gOddSwap_numerator_props (τ : ℍ) (m : ℕ) {F : ℂ → ℂ} (hF : F ∈ Θ2 τ .pp)
    {f : (Fin (m + (m + 1)) → ℂ) → ℂ} (hf : IsNumerator τ m (m + 1) F (gOddSwap τ m) f) :
    IsCanonShape τ (2 * (m + (m + 1))) m (m + 1) f ∧ C1 τ m (m + 1) f ∧ C2 m (m + 1) f := by
  have hG := gOdd_G τ m
  have hshape := shape_of_numerator_dev τ .pp hF (gOddSwap τ m)
    (fun x y a => by unfold gOddSwap; rw [(hG.2.2.1 y x a).1]; simp only [Eps.e1, one_mul])
    (fun x y a => by unfold gOddSwap; rw [(hG.2.2.1 y x a).2]; simp only [Eps.e2, one_mul])
    (fun x y k => by unfold gOddSwap; rw [(hG.2.1 y x k).1]; simp only [Eps.e1, one_mul])
    (fun x y k => by unfold gOddSwap; rw [(hG.2.1 y x k).2]; simp only [Eps.e2, one_mul])
    (fun x y a b hab => by unfold gOddSwap; exact hG.2.2.2.2 y x a b hab)
    (fun x y k l hkl => by unfold gOddSwap; exact hG.2.2.2.1 y x k l hkl) hf
  obtain ⟨f₀, R, hf₀, hR, hfac⟩ := gOddSwap_numerator_factor_dev τ m hF
  have heq := numerator_unique_dev τ hf hf₀
  have hfd : Differentiable ℂ f := by
    rw [heq, funext hfac]
    exact (((differentiable_Jfun_comp_dev τ _).pow 2).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul hR
  exact ⟨hshape, C1_of_factor_dev τ hshape (isOsgood_of_differentiable_dev hR) fun u => by rw [heq]; exact hfac u,
    C2_of_laurent_dev τ hF.1 hf hfd (wp_sub_inv_sq_analyticAt τ) fun a k x y hxy hgen =>
      gOddSwap_laurent_dev τ m a k x y hxy hgen⟩

/-- **Proposition C.explicit(b)** with **Lemma C.B(b)**: the numerator of `F(U) J² d^{(p)}_ε`, `F ∈ Θ_2[ε]`, exists. -/
theorem dEps_numerator_exists (τ : ℍ) (ε : Eps) (p : ℕ) {F : ℂ → ℂ} (hF : F ∈ Θ2 τ ε) :
    ∃ f, IsNumerator τ p p F (dEps τ ε p) f := by
  obtain ⟨f, -, hf, -⟩ := dEps_numerator_factor_dev τ ε p hF
  exact ⟨f, hf⟩

/-- **Proposition C.explicit(b)** with **Lemma C.B(b)**: shape at `L = 2N`, (C1), (C2). -/
theorem dEps_numerator_props (τ : ℍ) (ε : Eps) (p : ℕ) {F : ℂ → ℂ} (hF : F ∈ Θ2 τ ε)
    {f : (Fin (p + p) → ℂ) → ℂ} (hf : IsNumerator τ p p F (dEps τ ε p) f) :
    IsCanonShape τ (2 * (p + p)) p p f ∧ C1 τ p p f ∧ C2 p p f := by
  have hG := dEps_G τ ε p
  have hshape := shape_of_numerator_dev τ ε hF (dEps τ ε p) hG.2.1 hG.2.2.1 hG.2.2.2.1 hG.2.2.2.2.1
    hG.2.2.2.2.2.1 hG.2.2.2.2.2.2 hf
  obtain ⟨f₀, R, hf₀, hR, hfac⟩ := dEps_numerator_factor_dev τ ε p hF
  have heq := numerator_unique_dev τ hf hf₀
  have hfd : Differentiable ℂ f := by
    rw [heq, funext hfac]
    exact (((differentiable_Jfun_comp_dev τ _).pow 2).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul hR
  have hL : ∀ (a k : Fin p) (x y : Fin p → ℂ), x a = y k → (∀ a' k', (a' ≠ a ∨ k' ≠ k) → x a' - y k' ∉ Λu τ) →
      ∃ c : ℂ, ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ ∀ v,
        dEps τ ε p (Function.update x a (x a + v / 2)) (Function.update y k (y k - v / 2)) = c * wpE τ ε v + H v := by
    intro a k x y hxy hgen
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := a.isLt; omega⟩
    exact dEps_laurent_dev τ ε q a k x y hxy hgen
  exact ⟨hshape, C1_of_factor_dev τ hshape (isOsgood_of_differentiable_dev hR) fun u => by rw [heq]; exact hfac u,
    C2_of_laurent_dev τ hF.1 hf hfd (wpE_sub_inv_sq_analyticAt τ ε) hL⟩

/-- **Proposition C.explicit(c)** with **Lemma C.B(b)**: the numerator of `F(U) J² f_5^{(p)}`, `F ∈ Θ_2[(1,1)]`,
exists (`p = q + 1`). -/
theorem f5_numerator_exists (τ : ℍ) (q : ℕ) {F : ℂ → ℂ} (hF : F ∈ Θ2 τ .pp) :
    ∃ f, IsNumerator τ (q + 1) (q + 1) F (f5 τ q) f := by
  obtain ⟨f, -, hf, -⟩ := f5_numerator_factor_dev τ q hF
  exact ⟨f, hf⟩

/-- **Proposition C.explicit(c)** with **Lemma C.B(b)**: shape at `L = 2N`, (C1), (C2). -/
theorem f5_numerator_props (τ : ℍ) (q : ℕ) {F : ℂ → ℂ} (hF : F ∈ Θ2 τ .pp)
    {f : (Fin ((q + 1) + (q + 1)) → ℂ) → ℂ} (hf : IsNumerator τ (q + 1) (q + 1) F (f5 τ q) f) :
    IsCanonShape τ (2 * ((q + 1) + (q + 1))) (q + 1) (q + 1) f ∧ C1 τ (q + 1) (q + 1) f ∧
      C2 (q + 1) (q + 1) f := by
  have hG := f5_G τ q
  have hshape := shape_of_numerator_dev τ .pp hF (f5 τ q)
    (fun x y a => by rw [(hG.2.1 x y a).1]; simp only [Eps.e1, one_mul])
    (fun x y a => by rw [(hG.2.1 x y a).2]; simp only [Eps.e2, one_mul])
    (fun x y k => by rw [(hG.2.2.1 x y k).1]; simp only [Eps.e1, one_mul])
    (fun x y k => by rw [(hG.2.2.1 x y k).2]; simp only [Eps.e2, one_mul])
    hG.2.2.2.1 hG.2.2.2.2 hf
  obtain ⟨f₀, R, hf₀, hR, hfac⟩ := f5_numerator_factor_dev τ q hF
  have heq := numerator_unique_dev τ hf hf₀
  have hfd : Differentiable ℂ f := by
    rw [heq, funext hfac]
    exact (((differentiable_Jfun_comp_dev τ _).pow 2).mul ((differentiable_Jfun_comp_dev τ _).pow 2)).mul hR
  exact ⟨hshape, C1_of_factor_dev τ hshape (isOsgood_of_differentiable_dev hR) fun u => by rw [heq]; exact hfac u,
    C2_of_laurent_dev τ hF.1 hf hfd (wp_sub_inv_sq_analyticAt τ) fun a k x y hxy hgen =>
      f5_laurent_dev τ q a k x y hxy hgen⟩

/-! ### Proof devices for the merges (proof phase, round two; not statements of the paper)

The paper's argument ("`$\mu$ takes the coefficient of the $(1,1)$ entry.`"): expand along the first row
(`Matrix.det_succ_row_zero`); the `(1,1)` entry is `℘(v)` with `v²℘(v) → 1` (Lemma C.theta(d)–(e): `℘ − v⁻²` is
analytic at `0`), its cofactor is the matrix of the remaining variables; every other term is `v²` times a convergent
product (the other entries of the first row and column are continuous at `v = 0` at a generic point, the rest are
constant), so it tends to `0` (`merge_det_dev`, `merge_det_zero_dev`). `g_{2m+1}` is the determinant of the `℘`-matrix
of `(x, y ⧺ (w − ½))` with its last column replaced by ones, and `f_5^{(p)}` the sum over `j` of the determinants with
column `j` replaced by ones (`f5_eq_sum_dev`): both merge column by column (`merge_updateCol_dev`). -/

theorem tendsto_sq_zero_dev : Tendsto (fun v : ℂ => v ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  have h : Tendsto (fun v : ℂ => v ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) := (continuous_pow 2).tendsto 0
  rw [zero_pow two_ne_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- `v² P(v) → 1` when `P − v⁻²` is analytic at `0`. -/
theorem tendsto_sq_mul_of_dev {P : ℂ → ℂ} (hP : AnalyticAt ℂ (fun u => P u - 1 / u ^ 2) 0) :
    Tendsto (fun v => v ^ 2 * P v) (𝓝[≠] 0) (𝓝 1) := by
  have hc : Tendsto (fun u => P u - 1 / u ^ 2) (𝓝[≠] 0) (𝓝 (P 0 - 1 / 0 ^ 2)) :=
    hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := (tendsto_sq_zero_dev.mul hc).add (tendsto_const_nhds (x := (1 : ℂ)))
  rw [zero_mul, zero_add] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hv' : v ≠ 0 := hv
  field_simp
  ring

/-- `℘_ε` composed with a continuous function is continuous at `0` where the value is off the lattice. -/
theorem tendsto_wpE_comp_dev (τ : ℍ) (ε : Eps) {f : ℂ → ℂ} (hf : Continuous f) (hf0 : f 0 ∉ Λu τ) :
    Tendsto (fun v => wpE τ ε (f v)) (𝓝[≠] 0) (𝓝 (wpE τ ε (f 0))) :=
  (((wpE_analyticAt τ ε hf0).continuousAt.tendsto).comp (hf.tendsto 0)).mono_left nhdsWithin_le_nhds

/-- All entries convergent: `v² det M(v) → 0`. -/
theorem merge_det_zero_dev {n : ℕ} (M : ℂ → Matrix (Fin n) (Fin n) ℂ)
    (hconv : ∀ i j, ∃ l, Tendsto (fun v => M v i j) (𝓝[≠] 0) (𝓝 l)) :
    Tendsto (fun v => v ^ 2 * (M v).det) (𝓝[≠] 0) (𝓝 0) := by
  choose L hL using hconv
  have hmat : Tendsto M (𝓝[≠] 0) (𝓝 (Matrix.of L)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hL i j
  have hdet : Tendsto (fun v => (M v).det) (𝓝[≠] 0) (𝓝 (Matrix.of L).det) :=
    ((continuous_id.matrix_det).tendsto _).comp hmat
  have h := tendsto_sq_zero_dev.mul hdet
  rw [zero_mul] at h
  exact h

/-- The merge of a determinant: `v² det M(v) → det N` when `v² M(v)₀₀ → 1`, the rest of the first row and column
converge, and the lower right block is the constant `N`. -/
theorem merge_det_dev {n : ℕ} (M : ℂ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (N : Matrix (Fin n) (Fin n) ℂ)
    (h00 : Tendsto (fun v => v ^ 2 * M v 0 0) (𝓝[≠] 0) (𝓝 1))
    (hrow : ∀ j : Fin n, ∃ l, Tendsto (fun v => M v 0 j.succ) (𝓝[≠] 0) (𝓝 l))
    (hlow : ∀ (i : Fin n) (j : Fin (n + 1)), ∃ l, Tendsto (fun v => M v i.succ j) (𝓝[≠] 0) (𝓝 l))
    (hN : ∀ v (i j : Fin n), M v i.succ j.succ = N i j) :
    Tendsto (fun v => v ^ 2 * (M v).det) (𝓝[≠] 0) (𝓝 N.det) := by
  choose L hL using hlow
  have hsub : ∀ σ : Fin n → Fin (n + 1), Tendsto (fun v => ((M v).submatrix Fin.succ σ).det) (𝓝[≠] 0)
      (𝓝 ((Matrix.of fun i c => L i (σ c)).det)) := by
    intro σ
    have hmat : Tendsto (fun v => (M v).submatrix Fin.succ σ) (𝓝[≠] 0) (𝓝 (Matrix.of fun i c => L i (σ c))) :=
      tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun c => hL i (σ c)
    exact ((continuous_id.matrix_det).tendsto _).comp hmat
  have hsum : ∀ v, v ^ 2 * (M v).det = (v ^ 2 * M v 0 0) * N.det +
      ∑ j : Fin n, v ^ 2 * ((-1 : ℂ) ^ ((j.succ : Fin (n + 1)) : ℕ) * M v 0 j.succ *
        ((M v).submatrix Fin.succ j.succ.succAbove).det) := by
    intro v
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, mul_add, Finset.mul_sum]
    congr 1
    have e : (M v).submatrix Fin.succ (0 : Fin (n + 1)).succAbove = N := by
      ext i j
      simp [hN]
    rw [e]
    simp only [Fin.val_zero, pow_zero, one_mul]
    ring
  have hterm : ∀ j : Fin n, Tendsto (fun v => v ^ 2 * ((-1 : ℂ) ^ ((j.succ : Fin (n + 1)) : ℕ) * M v 0 j.succ *
      ((M v).submatrix Fin.succ j.succ.succAbove).det)) (𝓝[≠] 0) (𝓝 0) := by
    intro j
    obtain ⟨l, hl⟩ := hrow j
    have h := tendsto_sq_zero_dev.mul (((tendsto_const_nhds (x := (-1 : ℂ) ^ ((j.succ : Fin (n + 1)) : ℕ))).mul hl).mul (hsub j.succ.succAbove))
    rw [zero_mul] at h
    exact h
  have h := (h00.mul (tendsto_const_nhds (x := N.det))).add
    (tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun j _ => hterm j)
  rw [one_mul, Finset.sum_const_zero, add_zero] at h
  exact h.congr fun v => (hsum v).symm

/-- The merge of the `℘`-matrix with column `j` replaced by ones (for `j = 0` the limit is `0`). -/
theorem merge_updateCol_dev (τ : ℍ) {q : ℕ} (w : ℂ) (X' Y' : Fin q → ℂ)
    (hX : ∀ a, X' a - w ∉ Λu τ) (hY : ∀ k, w - Y' k ∉ Λu τ) (j : Fin (q + 1)) :
    Tendsto (fun v => v ^ 2 * ((Matrix.of fun (a k : Fin (q + 1)) =>
        wp τ ((Fin.cons (w + v / 2) X' : Fin (q + 1) → ℂ) a - (Fin.cons (w - v / 2) Y' : Fin (q + 1) → ℂ) k)).updateCol
          j fun _ => 1).det) (𝓝[≠] 0)
      (𝓝 (Fin.cases 0 (fun j' => ((Matrix.of fun (a k : Fin q) => wp τ (X' a - Y' k)).updateCol j'
        fun _ => 1).det) j)) := by
  have hrow0 : ∀ k : Fin q, Tendsto (fun v : ℂ => wp τ (w + v / 2 - Y' k)) (𝓝[≠] 0) (𝓝 (wp τ (w - Y' k))) := by
    intro k
    have h := tendsto_wpE_comp_dev τ .pp (f := fun v => w + v / 2 - Y' k) (by fun_prop) (by simpa using hY k)
    simp only [zero_div, add_zero] at h
    exact h
  have hcol0 : ∀ a : Fin q, Tendsto (fun v : ℂ => wp τ (X' a - (w - v / 2))) (𝓝[≠] 0) (𝓝 (wp τ (X' a - w))) := by
    intro a
    have h := tendsto_wpE_comp_dev τ .pp (f := fun v => X' a - (w - v / 2)) (by fun_prop) (by simpa using hX a)
    simp only [zero_div, sub_zero] at h
    exact h
  refine Fin.cases ?_ (fun j' => ?_) j
  · simp only [Fin.cases_zero]
    refine merge_det_zero_dev _ fun a k => ?_
    refine Fin.cases ?_ (fun a' => ?_) a <;> refine Fin.cases ?_ (fun k' => ?_) k
    · exact ⟨1, by simp⟩
    · exact ⟨wp τ (w - Y' k'), (hrow0 k').congr fun v => by simp [Fin.succ_ne_zero]⟩
    · exact ⟨1, by simp⟩
    · exact ⟨wp τ (X' a' - Y' k'), tendsto_const_nhds.congr fun v => by
        simp [Fin.succ_ne_zero]⟩
  · simp only [Fin.cases_succ]
    refine merge_det_dev _ _ ?_ (fun k => ?_) (fun a k => ?_) (fun v a k => ?_)
    · have h := tendsto_sq_mul_of_dev (wp_sub_inv_sq_analyticAt τ)
      refine h.congr fun v => ?_
      simp only [Matrix.updateCol_apply, (Fin.succ_ne_zero j').symm, ite_false, Matrix.of_apply, Fin.cons_zero]
      rw [show w + v / 2 - (w - v / 2) = v by ring]
    · by_cases hk : k = j'
      · subst hk
        exact ⟨1, by simp⟩
      · exact ⟨wp τ (w - Y' k), (hrow0 k).congr fun v => by
          simp [hk]⟩
    · refine Fin.cases ?_ (fun k' => ?_) k
      · exact ⟨wp τ (X' a - w), (hcol0 a).congr fun v => by
          simp [(Fin.succ_ne_zero j').symm]⟩
      · exact ⟨((Matrix.of fun (a k : Fin q) => wp τ (X' a - Y' k)).updateCol j' fun _ => 1) a k',
          tendsto_const_nhds.congr fun v => by simp [Matrix.updateCol_apply]⟩
    · simp [Matrix.updateCol_apply]


/-! ## The merge `μ` on the explicit functions -/

/-- The merge of Lemma C.C: "`=\lim_{v\to0}v^2g\big(w+\tfrac v2,x';w-\tfrac v2,y'\big)`" — `A` is the merge of `g` at
centre `w` with the other variables `x'`, `y'`. -/
def HasMerge {n m : ℕ} (g : (Fin (n + 1) → ℂ) → (Fin (m + 1) → ℂ) → ℂ) (w : ℂ) (x' : Fin n → ℂ)
    (y' : Fin m → ℂ) (A : ℂ) : Prop :=
  Tendsto (fun v : ℂ => v ^ 2 * g (Fin.cons (w + v / 2) x') (Fin.cons (w - v / 2) y')) (𝓝[≠] 0) (𝓝 A)

/-- A generic point for the merge: no up–down coincidence among the other variables, nor of the centre with them. -/
def MergeGeneric (τ : ℍ) {n m : ℕ} (w : ℂ) (x' : Fin n → ℂ) (y' : Fin m → ℂ) : Prop :=
  (∀ a k, x' a - y' k ∉ Λu τ) ∧ (∀ a, x' a - w ∉ Λu τ) ∧ ∀ k, w - y' k ∉ Λu τ

/-- **Proposition C.explicit(a)**: "`It lies in $\kzG(m+1,m;(1,1))$, with $\mu(g_{2m+1})=g_{2m-1}(x_2,\dots;y_2,\dots)$ and $\mu^m(g_{2m+1})=g_1=1$.`"
— the merge (the proof: "`$\mu$ takes the coefficient of the $(1,1)$ entry.`"). -/
theorem merge_gOdd (τ : ℍ) (m : ℕ) (w : ℂ) (x' : Fin (m + 1) → ℂ) (y' : Fin m → ℂ)
    (hgen : MergeGeneric τ w x' y') : HasMerge (gOdd τ (m + 1)) w x' y' (gOdd τ m x' y') := by
  -- `g_{2m+1}` as the `℘`-matrix of `(x, y ⧺ c)` with its last column replaced by ones, `c = 2w − x'₀` (so that the
  -- extra column's first entry is at a generic point; its entries do not enter)
  unfold HasMerge
  have hY : ∀ k : Fin (m + 1), w - (Fin.snoc y' (2 * w - x' 0) : Fin (m + 1) → ℂ) k ∉ Λu τ := by
    intro k
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · rw [Fin.snoc_last, show w - (2 * w - x' 0) = x' 0 - w by ring]
      exact hgen.2.1 0
    · rw [Fin.snoc_castSucc]
      exact hgen.2.2 k'
  have h := merge_updateCol_dev τ w x' (Fin.snoc y' (2 * w - x' 0)) hgen.2.1 hY (Fin.last m).succ
  simp only [Fin.cases_succ] at h
  rw [gOdd_eq_updateCol_dev τ m x' y' (2 * w - x' 0)]
  refine h.congr fun v => ?_
  rw [gOdd_eq_updateCol_dev τ (m + 1) _ _ (2 * w - x' 0), Fin.succ_last, Fin.cons_snoc_eq_snoc_cons]

/-- **Proposition C.explicit(a)**: "`$\mu^m(g_{2m+1})=g_1=1$`" — the end of the iteration, `g_1 = 1`. -/
theorem gOdd_zero (τ : ℍ) (x : Fin 1 → ℂ) (y : Fin 0 → ℂ) : gOdd τ 0 x y = 1 := by
  unfold gOdd
  rw [Matrix.det_fin_one]
  simp

/-- **Proposition C.explicit(b)**: "`$\mu(d^{(p)}_\varepsilon)=d^{(p-1)}_\varepsilon$`" (at `p + 1`; since `d^{(0)}_ε = 1`, at
`p = 0` it says that the merge of `℘_ε(x₁ − y₁)` is `1`, as in the proof of Proposition C.base: "`$\mu(\wp)=1$`"). -/
theorem merge_dEps (τ : ℍ) (ε : Eps) (p : ℕ) (w : ℂ) (x' y' : Fin p → ℂ) (hgen : MergeGeneric τ w x' y') :
    HasMerge (dEps τ ε (p + 1)) w x' y' (dEps τ ε p x' y') := by
  unfold HasMerge dEps
  refine merge_det_dev _ (Matrix.of fun i j => wpE τ ε (x' i - y' j)) ?_ (fun j => ?_) (fun i j => ?_)
    (fun v i j => ?_)
  · have h := tendsto_sq_mul_of_dev (wpE_sub_inv_sq_analyticAt τ ε)
    refine h.congr fun v => ?_
    simp only [Matrix.of_apply, Fin.cons_zero]
    rw [show w + v / 2 - (w - v / 2) = v by ring]
  · refine ⟨wpE τ ε (w - y' j), ?_⟩
    have h := tendsto_wpE_comp_dev τ ε (f := fun v => w + v / 2 - y' j) (by fun_prop) (by simpa using hgen.2.2 j)
    simp only [zero_div, add_zero] at h
    exact h.congr fun v => by simp
  · refine Fin.cases ?_ (fun j' => ?_) j
    · refine ⟨wpE τ ε (x' i - w), ?_⟩
      have h := tendsto_wpE_comp_dev τ ε (f := fun v => x' i - (w - v / 2)) (by fun_prop) (by simpa using hgen.2.1 i)
      simp only [zero_div, sub_zero] at h
      exact h.congr fun v => by simp
    · exact ⟨wpE τ ε (x' i - y' j'), tendsto_const_nhds.congr fun v => by simp⟩
  · simp

/-- **Proposition C.explicit(b)**: "`$\mu^{p-1}(d^{(p)}_\varepsilon)=\wp_\varepsilon$`" — the end of the iteration. -/
theorem dEps_one (τ : ℍ) (ε : Eps) (x y : Fin 1 → ℂ) : dEps τ ε 1 x y = wpE τ ε (x 0 - y 0) := by
  unfold dEps
  rw [Matrix.det_fin_one]
  rfl

/-- **Proposition C.explicit(c)**: "`with $\mu(f_5^{(p)})=f_5^{(p-1)}$ and $\mu^{p-1}(f_5^{(p)})=1$. In particular $d^{(p)}_{(1,1)}$ and $f_5^{(p)}$ are linearly independent.`"
— the merge. -/
theorem merge_f5 (τ : ℍ) (q : ℕ) (w : ℂ) (x' y' : Fin (q + 1) → ℂ) (hgen : MergeGeneric τ w x' y') :
    HasMerge (f5 τ (q + 1)) w x' y' (f5 τ q x' y') := by
  unfold HasMerge
  simp only [f5_eq_sum_dev, Finset.mul_sum]
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin (q + 2))) fun j _ =>
    merge_updateCol_dev τ w x' y' hgen.2.1 hgen.2.2 j
  rw [Fin.sum_univ_succ] at h
  simp only [Fin.cases_zero, Fin.cases_succ, zero_add] at h
  exact h

/-- **Proposition C.explicit(c)**: "`($f_5^{(1)}:=1$)`" — the end of the iteration. -/
theorem f5_zero (τ : ℍ) (x y : Fin 1 → ℂ) : f5 τ 0 x y = 1 := by
  unfold f5
  rw [Fin.sum_univ_one, Fin.sum_univ_one, Matrix.det_isEmpty]
  simp

/-! ### Proof devices for generic points (proof phase, round two; not statements of the paper)

`Λ_u` is the zero set of `ϑ₁` with simple zeros (Lemma C.theta(c)), so it is closed (`not_mem_Λu_nhds_dev`) and
discrete (`not_mem_Λu_punctured_dev`); it is countable, and a countable set of `ℂ` has dense complement (Mathlib's
`Set.Countable.dense_compl`), so a merge centre generic for given generic variables exists (`exists_mergeGeneric_dev`)
and the merge path stays generic on a punctured neighbourhood of `v = 0` (`eventually_generic_cons_dev`). -/

theorem exists_mergeGeneric_dev (τ : ℍ) {n m : ℕ} (x' : Fin n → ℂ) (y' : Fin m → ℂ) (hxy : Generic_dev τ x' y') :
    ∃ w, MergeGeneric τ w x' y' := by
  have hc : ((⋃ a, (fun l => x' a - l) '' Λu τ) ∪ ⋃ k, (fun l => y' k + l) '' Λu τ).Countable :=
    (Set.countable_iUnion fun a => (Λu_countable_dev τ).image _).union
      (Set.countable_iUnion fun k => (Λu_countable_dev τ).image _)
  obtain ⟨w, hw⟩ := (hc.dense_compl ℂ).nonempty
  refine ⟨w, hxy, fun a hmem => hw (Or.inl (Set.mem_iUnion.2 ⟨a, ⟨x' a - w, hmem, by ring⟩⟩)),
    fun k hmem => hw (Or.inr (Set.mem_iUnion.2 ⟨k, ⟨w - y' k, hmem, by ring⟩⟩))⟩

theorem eventually_generic_cons_dev (τ : ℍ) {n m : ℕ} (w : ℂ) (x' : Fin n → ℂ) (y' : Fin m → ℂ)
    (hgen : MergeGeneric τ w x' y') :
    ∀ᶠ v in 𝓝[≠] (0 : ℂ), Generic_dev τ (Fin.cons (w + v / 2) x' : Fin (n + 1) → ℂ)
      (Fin.cons (w - v / 2) y' : Fin (m + 1) → ℂ) := by
  have h00 : ∀ᶠ v in 𝓝[≠] (0 : ℂ), v ∉ Λu τ := not_mem_Λu_punctured_dev τ (zero_mem_Λu_dev τ)
  have hrow : ∀ k, ∀ᶠ v in 𝓝[≠] (0 : ℂ), w + v / 2 - y' k ∉ Λu τ := by
    intro k
    have hc : Tendsto (fun v : ℂ => w + v / 2 - y' k) (𝓝 0) (𝓝 (w - y' k)) := by
      have := (by fun_prop : Continuous fun v : ℂ => w + v / 2 - y' k).tendsto 0
      simpa using this
    exact (hc.eventually (not_mem_Λu_nhds_dev τ (hgen.2.2 k))).filter_mono nhdsWithin_le_nhds
  have hcol : ∀ a, ∀ᶠ v in 𝓝[≠] (0 : ℂ), x' a - (w - v / 2) ∉ Λu τ := by
    intro a
    have hc : Tendsto (fun v : ℂ => x' a - (w - v / 2)) (𝓝 0) (𝓝 (x' a - w)) := by
      have := (by fun_prop : Continuous fun v : ℂ => x' a - (w - v / 2)).tendsto 0
      simpa using this
    exact (hc.eventually (not_mem_Λu_nhds_dev τ (hgen.2.1 a))).filter_mono nhdsWithin_le_nhds
  filter_upwards [Filter.eventually_all.2 hrow, Filter.eventually_all.2 hcol, h00] with v hr hc h0
  intro a k
  refine Fin.cases ?_ (fun a' => ?_) a <;> refine Fin.cases ?_ (fun k' => ?_) k
  · simpa [show w + v / 2 - (w - v / 2) = v by ring] using h0
  · simpa using hr k'
  · simpa using hc a'
  · simpa using hgen.1 a' k'

/-- **Proposition C.explicit(c)**: "`In particular $d^{(p)}_{(1,1)}$ and $f_5^{(p)}$ are linearly independent.`" (with
Mathlib's `℘`; the module docstring for the additive constant). -/
theorem dEps_pp_f5_linearIndependent (τ : ℍ) (q : ℕ) :
    LinearIndependent ℂ ![fun (x y : Fin (q + 1) → ℂ) => dEps τ .pp (q + 1) x y, fun x y => f5 τ q x y] := by
  -- the paper's argument: the merges take `(d^{(p)}, f_5^{(p)})` to `(d^{(p−1)}, f_5^{(p−1)})` and, at the end,
  -- `(℘, 1)`, which are independent; by induction on the size, at generic points
  have key : ∀ (q : ℕ) (a b : ℂ), (∀ x y : Fin (q + 1) → ℂ, Generic_dev τ x y →
      a * dEps τ .pp (q + 1) x y + b * f5 τ q x y = 0) → a = 0 ∧ b = 0 := by
    intro q
    induction q with
    | zero =>
      intro a b h
      have hpt : ∀ᶠ v in 𝓝[≠] (0 : ℂ), a * wp τ v + b = 0 := by
        filter_upwards [not_mem_Λu_punctured_dev τ (zero_mem_Λu_dev τ)] with v hv
        have h1 := h ![v] ![0] (fun i k => by
          fin_cases i
          fin_cases k
          simpa using hv)
        rw [dEps_one, f5_zero] at h1
        simpa [wpE] using h1
      have hlim : Tendsto (fun v => v ^ 2 * (a * wp τ v + b)) (𝓝[≠] 0) (𝓝 a) := by
        have h1 := (tendsto_sq_mul_of_dev (wp_sub_inv_sq_analyticAt τ)).const_mul a
        have h2 := tendsto_sq_zero_dev.mul_const b
        have h3 := h1.add h2
        rw [mul_one, zero_mul, add_zero] at h3
        exact h3.congr fun v => by ring
      have hzero : Tendsto (fun v => v ^ 2 * (a * wp τ v + b)) (𝓝[≠] 0) (𝓝 0) :=
        tendsto_const_nhds.congr' (by
          filter_upwards [hpt] with v hv
          rw [hv, mul_zero])
      have ha : a = 0 := tendsto_nhds_unique hlim hzero
      obtain ⟨v, hv⟩ := hpt.exists
      rw [ha, zero_mul, zero_add] at hv
      exact ⟨ha, hv⟩
    | succ q ih =>
      intro a b h
      refine ih a b fun x' y' hxy => ?_
      obtain ⟨w, hw⟩ := exists_mergeGeneric_dev τ x' y' hxy
      have hev : ∀ᶠ v in 𝓝[≠] (0 : ℂ), v ^ 2 * (a * dEps τ .pp (q + 1 + 1) (Fin.cons (w + v / 2) x')
          (Fin.cons (w - v / 2) y') + b * f5 τ (q + 1) (Fin.cons (w + v / 2) x') (Fin.cons (w - v / 2) y')) = 0 := by
        filter_upwards [eventually_generic_cons_dev τ w x' y' hw] with v hv
        rw [h _ _ hv, mul_zero]
      have hlim := ((merge_dEps τ .pp (q + 1) w x' y' hw).const_mul a).add ((merge_f5 τ q w x' y' hw).const_mul b)
      have hlim' : Tendsto (fun v => v ^ 2 * (a * dEps τ .pp (q + 1 + 1) (Fin.cons (w + v / 2) x')
          (Fin.cons (w - v / 2) y') + b * f5 τ (q + 1) (Fin.cons (w + v / 2) x') (Fin.cons (w - v / 2) y')))
          (𝓝[≠] 0) (𝓝 (a * dEps τ .pp (q + 1) x' y' + b * f5 τ q x' y')) :=
        hlim.congr fun v => by ring
      exact tendsto_nhds_unique hlim' (tendsto_const_nhds.congr' (hev.mono fun v hv => hv.symm))
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hpt : ∀ x y : Fin (q + 1) → ℂ, g 0 * dEps τ .pp (q + 1) x y + g 1 * f5 τ q x y = 0 := by
    intro x y
    have := congrFun (congrFun hg x) y
    simpa [Fin.sum_univ_two] using this
  obtain ⟨h0, h1⟩ := key q (g 0) (g 1) fun x y _ => hpt x y
  exact Fin.forall_fin_two.2 ⟨h0, h1⟩

/-! ### Proof device for the centre-of-mass factors (proof phase, round two; not a statement of the paper): `2τ ∈ ℍ` -/

def tau2_dev (τ : ℍ) : ℍ :=
  ⟨2 * (τ : ℂ), by simpa [Complex.mul_im] using mul_pos (two_pos : (0 : ℝ) < 2) τ.coe_im_pos⟩

/-! ### Proof devices for the independence of the states (proof phase, round two; not statements of the paper)

At a point with all differences off the lattice (`FG2_dev`: then `J ≠ 0`, `Jfun_ne_zero_dev`, and the point is off the
polar set) where `g ≠ 0` — such points exist, by the merges, which take `g` down to `1` (`exists_FG2_gOdd_dev`,
`exists_FG2_dEps_dev`) — translating every variable by a common `c` moves `U` anywhere and changes neither `J²` nor `g`,
so `Σ_r c_r F_r(U) = 0` for every `U` (`li_of_numerators_dev`). Across `ε` (Lemma C.B's "`the spaces for different $\varepsilon$ have different multipliers under $c\mapsto c+1/N$ and $c\mapsto c+\tau/N$`"),
the translations by `1/N` and `τ/N` multiply the state of `F ∈ Θ_2[ε]` by `ε₁⁻¹` and by `ε₂⁻¹` times a common factor,
which separates the four classes (`sep_eps_dev`); inside `ε = (1,1)` the merges separate `d^{(p)}_{(1,1)}` from
`f_5^{(p)}` at points with all differences off the lattice (`key_pp_dev`, as in `dEps_pp_f5_linearIndependent`). -/

/-- All differences off the lattice, within each species and between them. -/
def FG2_dev (τ : ℍ) {n m : ℕ} (x : Fin n → ℂ) (y : Fin m → ℂ) : Prop :=
  (∀ a b, a ≠ b → x a - x b ∉ Λu τ) ∧ (∀ k l, k ≠ l → y k - y l ∉ Λu τ) ∧ Generic_dev τ x y

theorem FG2_swap_dev (τ : ℍ) {n m : ℕ} {x : Fin n → ℂ} {y : Fin m → ℂ} (h : FG2_dev τ x y) : FG2_dev τ y x :=
  ⟨h.2.1, h.1, fun k a hmem => h.2.2 a k (by simpa using neg_mem_Λu_dev τ hmem)⟩

theorem Jfun_ne_zero_dev (τ : ℍ) {N : ℕ} (u : Fin N → ℂ) (h : ∀ i j, i < j → u i - u j ∉ Λu τ) :
    Jfun τ u ≠ 0 := by
  unfold Jfun
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact fun h0 => h i j hj ((theta1_eq_zero_iff τ _).1 h0)

theorem eventually_FG2_cons_dev (τ : ℍ) {n m : ℕ} (w : ℂ) (x' : Fin n → ℂ) (y' : Fin m → ℂ)
    (hfg : FG2_dev τ x' y') (hgen : MergeGeneric τ w x' y') :
    ∀ᶠ v in 𝓝[≠] (0 : ℂ), FG2_dev τ (Fin.cons (w + v / 2) x' : Fin (n + 1) → ℂ)
      (Fin.cons (w - v / 2) y' : Fin (m + 1) → ℂ) := by
  have hev : ∀ f : ℂ → ℂ, Continuous f → f 0 ∉ Λu τ → ∀ᶠ v in 𝓝[≠] (0 : ℂ), f v ∉ Λu τ := fun f hf h0 =>
    ((hf.tendsto 0).eventually (not_mem_Λu_nhds_dev τ h0)).filter_mono nhdsWithin_le_nhds
  have hxw : ∀ a, w - x' a ∉ Λu τ := fun a hmem => hgen.2.1 a (by simpa using neg_mem_Λu_dev τ hmem)
  have hyw : ∀ k, y' k - w ∉ Λu τ := fun k hmem => hgen.2.2 k (by simpa using neg_mem_Λu_dev τ hmem)
  have e1 : ∀ b, ∀ᶠ v in 𝓝[≠] (0 : ℂ), w + v / 2 - x' b ∉ Λu τ := fun b =>
    hev (fun v => w + v / 2 - x' b) (by fun_prop) (by simpa using hxw b)
  have e2 : ∀ a, ∀ᶠ v in 𝓝[≠] (0 : ℂ), x' a - (w + v / 2) ∉ Λu τ := fun a =>
    hev (fun v => x' a - (w + v / 2)) (by fun_prop) (by simpa using hgen.2.1 a)
  have e3 : ∀ l, ∀ᶠ v in 𝓝[≠] (0 : ℂ), w - v / 2 - y' l ∉ Λu τ := fun l =>
    hev (fun v => w - v / 2 - y' l) (by fun_prop) (by simpa using hgen.2.2 l)
  have e4 : ∀ k, ∀ᶠ v in 𝓝[≠] (0 : ℂ), y' k - (w - v / 2) ∉ Λu τ := fun k =>
    hev (fun v => y' k - (w - v / 2)) (by fun_prop) (by simpa using hyw k)
  filter_upwards [Filter.eventually_all.2 e1, Filter.eventually_all.2 e2, Filter.eventually_all.2 e3,
    Filter.eventually_all.2 e4, eventually_generic_cons_dev τ w x' y' hgen] with v h1 h2 h3 h4 h5
  refine ⟨fun a b hab => ?_, fun k l hkl => ?_, h5⟩
  · induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact absurd rfl hab
      | succ b' => simpa using h1 b'
    | succ a' =>
      induction b using Fin.cases with
      | zero => simpa using h2 a'
      | succ b' => simpa using hfg.1 a' b' (fun h => hab (by rw [h]))
  · induction k using Fin.cases with
    | zero =>
      induction l using Fin.cases with
      | zero => exact absurd rfl hkl
      | succ l' => simpa using h3 l'
    | succ k' =>
      induction l using Fin.cases with
      | zero => simpa using h4 k'
      | succ l' => simpa using hfg.2.1 k' l' (fun h => hkl (by rw [h]))

theorem exists_FG2_gOdd_dev (τ : ℍ) :
    ∀ m : ℕ, ∃ (x : Fin (m + 1) → ℂ) (y : Fin m → ℂ), FG2_dev τ x y ∧ gOdd τ m x y ≠ 0 := by
  intro m
  induction m with
  | zero =>
    refine ⟨fun _ => 0, fun i => i.elim0,
      ⟨fun a b hab => absurd (Fin.ext (by have := a.isLt; have := b.isLt; omega)) hab, fun k => k.elim0, fun _ k => k.elim0⟩, ?_⟩
    rw [gOdd_zero]
    exact one_ne_zero
  | succ m ih =>
    obtain ⟨x', y', hfg, hne⟩ := ih
    obtain ⟨w, hw⟩ := exists_mergeGeneric_dev τ x' y' hfg.2.2
    have hne' := (merge_gOdd τ m w x' y' hw).eventually_ne hne
    obtain ⟨v, hv1, hv2⟩ := (hne'.and (eventually_FG2_cons_dev τ w x' y' hfg hw)).exists
    exact ⟨_, _, hv2, fun h => hv1 (by rw [h, mul_zero])⟩

theorem exists_FG2_dEps_dev (τ : ℍ) (ε : Eps) :
    ∀ p : ℕ, ∃ x y : Fin p → ℂ, FG2_dev τ x y ∧ dEps τ ε p x y ≠ 0 := by
  intro p
  induction p with
  | zero =>
    refine ⟨fun i => i.elim0, fun i => i.elim0, ⟨fun a => a.elim0, fun k => k.elim0, fun a => a.elim0⟩, ?_⟩
    rw [dEps, Matrix.det_isEmpty]
    exact one_ne_zero
  | succ p ih =>
    obtain ⟨x', y', hfg, hne⟩ := ih
    obtain ⟨w, hw⟩ := exists_mergeGeneric_dev τ x' y' hfg.2.2
    have hne' := (merge_dEps τ ε p w x' y' hw).eventually_ne hne
    obtain ⟨v, hv1, hv2⟩ := (hne'.and (eventually_FG2_cons_dev τ w x' y' hfg hw)).exists
    exact ⟨_, _, hv2, fun h => hv1 (by rw [h, mul_zero])⟩

/-- The point `(x₀ + c, y₀ + c)` with total `U`, off the polar set, with `J ≠ 0`. -/
theorem translate_point_dev (τ : ℍ) {n m : ℕ} (hN : n + m ≠ 0) (x₀ : Fin n → ℂ) (y₀ : Fin m → ℂ)
    (hfg : FG2_dev τ x₀ y₀) (U : ℂ) :
    ∃ u : Fin (n + m) → ℂ, ∑ i, u i = U ∧ u ∉ polarSet τ n m ∧ Jfun τ u ≠ 0 ∧
      ∃ c : ℂ, (fun a => u (Fin.castAdd m a)) = (fun a => x₀ a + c) ∧ (fun k => u (Fin.natAdd n k)) = fun k => y₀ k + c := by
  have hN0 : ((n + m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN
  set c : ℂ := (U - (∑ a, x₀ a + ∑ k, y₀ k)) / ((n + m : ℕ) : ℂ) with hc
  refine ⟨Fin.append (fun a => x₀ a + c) (fun k => y₀ k + c), ?_, ?_, ?_, c, by funext a; simp, by funext k; simp⟩
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [hc]
    field_simp
    push_cast
    ring
  · rintro ⟨a, k, hmem⟩
    apply hfg.2.2 a k
    simpa using hmem
  · rw [Jfun_append_dev]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact Jfun_ne_zero_dev τ _ fun a b hab => by simpa using hfg.1 a b hab.ne
    · exact Jfun_ne_zero_dev τ _ fun k l hkl => by simpa using hfg.2.1 k l hkl.ne
    · refine Finset.prod_ne_zero_iff.2 fun a _ => Finset.prod_ne_zero_iff.2 fun k _ => ?_
      exact fun h0 => hfg.2.2 a k (by simpa using (theta1_eq_zero_iff τ _).1 h0)

/-- Two (or more) independent `F`, one `g`: the numerators are independent. -/
theorem li_of_numerators_dev (τ : ℍ) {n m : ℕ} (hN : n + m ≠ 0) (g : (Fin n → ℂ) → (Fin m → ℂ) → ℂ)
    (hg_tr : ∀ x y c, g (fun i => x i + c) (fun j => y j + c) = g x y)
    (x₀ : Fin n → ℂ) (y₀ : Fin m → ℂ) (hfg : FG2_dev τ x₀ y₀) (hne : g x₀ y₀ ≠ 0)
    {ι : Type*} [Fintype ι] (F : ι → ℂ → ℂ) (hFi : LinearIndependent ℂ F) (f : ι → (Fin (n + m) → ℂ) → ℂ)
    (hf : ∀ r, IsNumerator τ n m (F r) g (f r)) : LinearIndependent ℂ f := by
  rw [Fintype.linearIndependent_iff] at hFi ⊢
  intro c hc
  refine hFi c (funext fun U => ?_)
  obtain ⟨u, hsum, hpol, hJ, c', hux, huy⟩ := translate_point_dev τ hN x₀ y₀ hfg U
  have hfu : ∀ r, f r u = F r U * (Jfun τ u ^ 2 * g x₀ y₀) := by
    intro r
    rw [(hf r).2 u hpol, stateFun, hsum, hux, huy, hg_tr]
    ring
  have h0 := congrFun hc u
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hfu] at h0
  have h1 : (∑ r, c r * F r U) * (Jfun τ u ^ 2 * g x₀ y₀) = 0 := by
    rw [Finset.sum_mul]
    rw [← h0]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hK : Jfun τ u ^ 2 * g x₀ y₀ ≠ 0 := mul_ne_zero (pow_ne_zero 2 hJ) hne
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  exact (mul_eq_zero.1 h1).resolve_right hK

theorem e1_inv_dev (ε : Eps) : (ε.e1)⁻¹ = ε.e1 := by
  cases ε <;> norm_num [Eps.e1]

theorem e2_inv_dev (ε : Eps) : (ε.e2)⁻¹ = ε.e2 := by
  cases ε <;> norm_num [Eps.e2]

theorem sum_eps_dev {M : Type*} [AddCommMonoid M] (f : Eps → M) :
    ∑ ε, f ε = f .pp + f .mp + f .pm + f .mm := by
  rw [show (Finset.univ : Finset Eps) = {Eps.pp, Eps.mp, Eps.pm, Eps.mm} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

/-- Functions of the four spaces `Θ_2[ε]` summing to zero are zero (the multipliers under `U ↦ U + 1`, `U ↦ U + τ`). -/
theorem sep_eps_dev (τ : ℍ) (Φ : Eps → ℂ → ℂ) (hΦ : ∀ ε, Φ ε ∈ Θ2 τ ε) (hsum : ∀ U, ∑ ε, Φ ε U = 0) :
    ∀ ε, Φ ε = 0 := by
  have h1 : ∀ ε U, Φ ε (U + 1) = ε.e1 * Φ ε U := fun ε U => by rw [(hΦ ε).2.1 U, e1_inv_dev]
  have h2 : ∀ ε U, Φ ε (U + τ) = ε.e2 * cexp (-4 * π * I * U - 2 * π * I * τ) * Φ ε U := fun ε U => by
    rw [(hΦ ε).2.2 U, e2_inv_dev]
  intro ε
  funext U
  simp only [Pi.zero_apply]
  have e0 := hsum U
  have e1 := hsum (U + 1)
  have e2 := hsum (U + τ)
  have e3 := hsum (U + 1 + τ)
  simp only [sum_eps_dev] at e0 e1 e2 e3
  rw [h1, h1, h1, h1] at e1
  rw [h2, h2, h2, h2] at e2
  rw [h2, h2, h2, h2, h1, h1, h1, h1] at e3
  simp only [Eps.e1, Eps.e2] at e1 e2 e3
  have hE : cexp (-4 * π * I * U - 2 * π * I * τ) ≠ 0 := Complex.exp_ne_zero _
  have hE' : cexp (-4 * π * I * (U + 1) - 2 * π * I * τ) ≠ 0 := Complex.exp_ne_zero _
  have e2' : Φ .pp U + Φ .mp U - Φ .pm U - Φ .mm U = 0 := by
    have h : cexp (-4 * π * I * U - 2 * π * I * τ) * (Φ .pp U + Φ .mp U - Φ .pm U - Φ .mm U) = 0 := by
      linear_combination e2
    exact (mul_eq_zero.1 h).resolve_left hE
  have e3' : Φ .pp U - Φ .mp U - Φ .pm U + Φ .mm U = 0 := by
    have h : cexp (-4 * π * I * (U + 1) - 2 * π * I * τ) * (Φ .pp U - Φ .mp U - Φ .pm U + Φ .mm U) = 0 := by
      linear_combination e3
    exact (mul_eq_zero.1 h).resolve_left hE'
  cases ε
  · linear_combination (e0 + e1 + e2' + e3') / 4
  · linear_combination (e0 - e1 + e2' - e3') / 4
  · linear_combination (e0 + e1 - e2' - e3') / 4
  · linear_combination (e0 - e1 - e2' + e3') / 4

/-- `d^{(p)}_{(1,1)}` and `f_5^{(p)}` are independent already on the points with all differences off the lattice. -/
theorem key_pp_FG2_dev (τ : ℍ) : ∀ (q : ℕ) (a b : ℂ), (∀ x y : Fin (q + 1) → ℂ, FG2_dev τ x y →
    a * dEps τ .pp (q + 1) x y + b * f5 τ q x y = 0) → a = 0 ∧ b = 0 := by
  intro q
  induction q with
  | zero =>
    intro a b h
    have hpt : ∀ᶠ v in 𝓝[≠] (0 : ℂ), a * wp τ v + b = 0 := by
      filter_upwards [not_mem_Λu_punctured_dev τ (zero_mem_Λu_dev τ)] with v hv
      have h1 := h ![v] ![0] ⟨fun a b hab => absurd (Fin.ext (by have := a.isLt; have := b.isLt; omega)) hab,
        fun k l hkl => absurd (Fin.ext (by have := k.isLt; have := l.isLt; omega)) hkl, fun i k => by
          fin_cases i
          fin_cases k
          simpa using hv⟩
      rw [dEps_one, f5_zero] at h1
      simpa [wpE] using h1
    have hlim : Tendsto (fun v => v ^ 2 * (a * wp τ v + b)) (𝓝[≠] 0) (𝓝 a) := by
      have h1 := (tendsto_sq_mul_of_dev (wp_sub_inv_sq_analyticAt τ)).const_mul a
      have h2 := tendsto_sq_zero_dev.mul_const b
      have h3 := h1.add h2
      rw [mul_one, zero_mul, add_zero] at h3
      exact h3.congr fun v => by ring
    have hzero : Tendsto (fun v => v ^ 2 * (a * wp τ v + b)) (𝓝[≠] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [hpt] with v hv
        rw [hv, mul_zero])
    have ha : a = 0 := tendsto_nhds_unique hlim hzero
    obtain ⟨v, hv⟩ := hpt.exists
    rw [ha, zero_mul, zero_add] at hv
    exact ⟨ha, hv⟩
  | succ q ih =>
    intro a b h
    refine ih a b fun x' y' hfg => ?_
    obtain ⟨w, hw⟩ := exists_mergeGeneric_dev τ x' y' hfg.2.2
    have hev : ∀ᶠ v in 𝓝[≠] (0 : ℂ), v ^ 2 * (a * dEps τ .pp (q + 1 + 1) (Fin.cons (w + v / 2) x')
        (Fin.cons (w - v / 2) y') + b * f5 τ (q + 1) (Fin.cons (w + v / 2) x') (Fin.cons (w - v / 2) y')) = 0 := by
      filter_upwards [eventually_FG2_cons_dev τ w x' y' hfg hw] with v hv
      rw [h _ _ hv, mul_zero]
    have hlim := ((merge_dEps τ .pp (q + 1) w x' y' hw).const_mul a).add ((merge_f5 τ q w x' y' hw).const_mul b)
    have hlim' : Tendsto (fun v => v ^ 2 * (a * dEps τ .pp (q + 1 + 1) (Fin.cons (w + v / 2) x')
        (Fin.cons (w - v / 2) y') + b * f5 τ (q + 1) (Fin.cons (w + v / 2) x') (Fin.cons (w - v / 2) y')))
        (𝓝[≠] 0) (𝓝 (a * dEps τ .pp (q + 1) x' y' + b * f5 τ q x' y')) :=
      hlim.congr fun v => by ring
    exact tendsto_nhds_unique hlim' (tendsto_const_nhds.congr' (hev.mono fun v hv => hv.symm))

theorem gEven_tr_dev (τ : ℍ) (q : ℕ) (e : Option Eps) (x y : Fin (q + 1) → ℂ) (c : ℂ) :
    gEven τ q e (fun i => x i + c) (fun j => y j + c) = gEven τ q e x y := by
  cases e with
  | none => exact (f5_G τ q).1 x y c
  | some ε => exact (dEps_G τ ε (q + 1)).1 x y c

/-! ## The centre-of-mass factors and the independence of the states -/

/-- **Theorem C.T2(ii)** (proof): "`$\kzTh_2[(1,1)]$ is spanned by $\kzvth[a,0](2U|2\tau)$, $a\in\{0,\tfrac12\}$`" —
membership. -/
theorem thetaK_mem (τ : ℍ) {a : ℝ} (ha : a = 0 ∨ a = 1 / 2) :
    (fun U => thetaChar a 0 (2 * U) (2 * (τ : ℂ))) ∈ Θ2 τ .pp := by
  have ha' : cexp (2 * π * I * a) * cexp (2 * π * I * a) = 1 := by
    rcases ha with rfl | rfl
    · simp
    · rw [exp_two_pi_I_half_dev]
      norm_num
  refine ⟨?_, fun U => ?_, fun U => ?_⟩
  · exact (thetaChar_differentiable a 0 (tau2_dev τ)).comp (differentiable_id.const_mul 2)
  · show thetaChar a 0 (2 * (U + 1)) (2 * (τ : ℂ)) = (Eps.pp.e1)⁻¹ * thetaChar a 0 (2 * U) (2 * (τ : ℂ))
    rw [show 2 * (U + 1) = 2 * U + 1 + 1 by ring, thetaChar_add_one, thetaChar_add_one, ← mul_assoc, ha']
    simp [Eps.e1]
  · show thetaChar a 0 (2 * (U + τ)) (2 * (τ : ℂ)) =
      (Eps.pp.e2)⁻¹ * cexp (-4 * π * I * U - 2 * π * I * τ) * thetaChar a 0 (2 * U) (2 * (τ : ℂ))
    rw [show 2 * (U + (τ : ℂ)) = 2 * U + 2 * (τ : ℂ) by ring, thetaChar_add_tau]
    simp only [Eps.e2, inv_one, one_mul]
    congr 2
    push_cast
    ring

/-- **Theorem C.T2(ii)** (proof): the two centre-of-mass factors `ϑ[0,0](2U|2τ)`, `ϑ[½,0](2U|2τ)` are independent (so they
span the two-dimensional `Θ_2[(1,1)]`). -/
theorem thetaK_linearIndependent (τ : ℍ) :
    LinearIndependent ℂ ![fun U => thetaChar 0 0 (2 * U) (2 * (τ : ℂ)), fun U => thetaChar (1 / 2) 0 (2 * U) (2 * (τ : ℂ))] := by
  have hbasis : ∀ (r : ℕ) (U : ℂ), thetaChar ((r : ℝ) / 2) 0 (2 * U) (2 * (τ : ℂ)) =
      cexp (π * I * (r : ℂ) ^ 2 * τ / 2) * ThetaDev.thetaBasis τ 0 0 2 r U := by
    intro r U
    unfold thetaChar ThetaDev.thetaBasis
    rw [show ∀ a b c : ℂ, cexp a * (cexp b * c) = cexp (a + b) * c from fun a b c => by rw [Complex.exp_add, mul_assoc]]
    congr 1
    · congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring
  have hnz : ∀ r : ℕ, r < 2 → ∃ U, thetaChar ((r : ℝ) / 2) 0 (2 * U) (2 * (τ : ℂ)) ≠ 0 := by
    intro r hr
    by_contra hall
    push Not at hall
    have h0 : ThetaDev.thetaBasis τ 0 0 2 r = 0 := by
      funext U
      have := hall U
      rw [hbasis] at this
      exact (mul_eq_zero.1 this).resolve_left (Complex.exp_ne_zero _)
    have hc := ThetaDev.coef_thetaBasis τ.coe_im_pos 0 0 (by norm_num : 0 < 2) hr hr
    rw [h0] at hc
    simp [ThetaDev.coef] at hc
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hpt : ∀ U, g 0 * thetaChar 0 0 (2 * U) (2 * (τ : ℂ)) + g 1 * thetaChar (1 / 2) 0 (2 * U) (2 * (τ : ℂ)) = 0 := by
    intro U
    have := congrFun hg U
    simpa [Fin.sum_univ_two] using this
  have hshift : ∀ U, g 0 * thetaChar 0 0 (2 * U) (2 * (τ : ℂ)) - g 1 * thetaChar (1 / 2) 0 (2 * U) (2 * (τ : ℂ)) = 0 := by
    intro U
    have h := hpt (U + 1 / 2)
    rw [show 2 * (U + 1 / 2) = 2 * U + 1 by ring, thetaChar_add_one, thetaChar_add_one, exp_two_pi_I_half_dev] at h
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h
    linear_combination h
  have h0 : ∀ U, g 0 * thetaChar 0 0 (2 * U) (2 * (τ : ℂ)) = 0 := fun U => by
    linear_combination (hpt U + hshift U) / 2
  have h1 : ∀ U, g 1 * thetaChar (1 / 2) 0 (2 * U) (2 * (τ : ℂ)) = 0 := fun U => by
    linear_combination (hpt U - hshift U) / 2
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · obtain ⟨U, hU⟩ := hnz 0 (by norm_num)
    simp only [Nat.cast_zero, zero_div] at hU
    exact (mul_eq_zero.1 (h0 U)).resolve_right hU
  · obtain ⟨U, hU⟩ := hnz 1 (by norm_num)
    simp only [Nat.cast_one] at hU
    exact (mul_eq_zero.1 (h1 U)).resolve_right hU

/-- **Theorem C.T2(iii)**: "`It is spanned by $F(U)J^2g$ with $g\in\{d^{(p)}_\varepsilon:\varepsilon\in\{\pm1\}^2\}\cup\{f_5^{(p)}\}$ and $F\in\kzTh_2[\varepsilon]$, two for each $g$.`"
— the independence half: for `N = 2p`, `p = q + 1`, the ten numerators (two independent `F ∈ Θ_2[ε]` for each of the
five `g`) are linearly independent (the proof of Theorem C.T2(iii): "`Proposition~\ref{kz:prop:explicit}(b),(c) gives five independent relative states (independent across $\varepsilon$ by Lemma~\ref{kz:lem:B}(b)), so equality holds.`";
Lemma C.B's "`the spaces for different $\varepsilon$ have different multipliers under $c\mapsto c+1/N$ and $c\mapsto c+\tau/N$`"). -/
theorem explicit_even_linearIndependent (τ : ℍ) (q : ℕ) (F : Option Eps → Fin 2 → ℂ → ℂ)
    (hF : ∀ e r, F e r ∈ Θ2 τ (epsOf e)) (hFi : ∀ e, LinearIndependent ℂ (F e))
    (f : Option Eps × Fin 2 → (Fin ((q + 1) + (q + 1)) → ℂ) → ℂ)
    (hf : ∀ i, IsNumerator τ (q + 1) (q + 1) (F i.1 i.2) (gEven τ q i.1) (f i)) :
    LinearIndependent ℂ f := by
  have _ := hF
  have hN : (q + 1) + (q + 1) ≠ 0 := by omega
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- at every point with all differences off the lattice: `Σ_i c_i g_{e_i}(x₀, y₀) F_i = 0`
  have hΦ : ∀ x₀ y₀ : Fin (q + 1) → ℂ, FG2_dev τ x₀ y₀ → ∀ U : ℂ,
      ∑ i : Option Eps × Fin 2, c i * gEven τ q i.1 x₀ y₀ * F i.1 i.2 U = 0 := by
    intro x₀ y₀ hfg U
    obtain ⟨u, hsum, hpol, hJ, c', hux, huy⟩ := translate_point_dev τ hN x₀ y₀ hfg U
    have h0 := congrFun hc u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    have hfu : ∀ i, f i u = Jfun τ u ^ 2 * (gEven τ q i.1 x₀ y₀ * F i.1 i.2 U) := by
      intro i
      rw [(hf i).2 u hpol, stateFun, hsum, hux, huy, gEven_tr_dev]
      ring
    simp only [hfu] at h0
    have h1 : Jfun τ u ^ 2 * ∑ i, c i * gEven τ q i.1 x₀ y₀ * F i.1 i.2 U = 0 := by
      rw [Finset.mul_sum, ← h0]
      exact Finset.sum_congr rfl fun i _ => by ring
    exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero 2 hJ)
  -- the four multiplier classes separately
  have hclass : ∀ x₀ y₀ : Fin (q + 1) → ℂ, FG2_dev τ x₀ y₀ → ∀ ε : Eps,
      (fun U => ∑ r, c (some ε, r) * dEps τ ε (q + 1) x₀ y₀ * F (some ε) r U +
        if ε = .pp then ∑ r, c (none, r) * f5 τ q x₀ y₀ * F none r U else 0) = 0 := by
    intro x₀ y₀ hfg
    refine sep_eps_dev τ _ (fun ε => ?_) (fun U => ?_)
    · have e : (fun U => ∑ r, c (some ε, r) * dEps τ ε (q + 1) x₀ y₀ * F (some ε) r U +
          if ε = .pp then ∑ r, c (none, r) * f5 τ q x₀ y₀ * F none r U else 0) =
          (∑ r, (c (some ε, r) * dEps τ ε (q + 1) x₀ y₀) • F (some ε) r) +
            (if ε = .pp then ∑ r, (c (none, r) * f5 τ q x₀ y₀) • F none r else 0) := by
        funext U
        split_ifs <;> simp [mul_assoc]
      rw [e]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (hF (some ε) r)) ?_
      split_ifs with hε
      · subst hε
        exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (hF none r)
      · exact Submodule.zero_mem _
    · have h := hΦ x₀ y₀ hfg U
      rw [Fintype.sum_prod_type, Fintype.sum_option] at h
      simp only [gEven] at h
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      linear_combination h
  have hsome : ∀ ε : Eps, ε ≠ .pp → ∀ r, c (some ε, r) = 0 := by
    intro ε hε
    obtain ⟨x₀, y₀, hfg, hne⟩ := exists_FG2_dEps_dev τ ε (q + 1)
    have h := hclass x₀ y₀ hfg ε
    simp only [hε, ite_false, add_zero] at h
    have hli := Fintype.linearIndependent_iff.1 (hFi (some ε)) (fun r => c (some ε, r) * dEps τ ε (q + 1) x₀ y₀)
      (by
        funext U
        have := congrFun h U
        simpa [Finset.sum_apply] using this)
    intro r
    exact (mul_eq_zero.1 (hli r)).resolve_right hne
  have hpp : ∀ r, c (some .pp, r) = 0 ∧ c (none, r) = 0 := by
    have hAB : ∀ U, (∑ r, c (some .pp, r) * F (some .pp) r U) = 0 ∧ (∑ r, c (none, r) * F none r U) = 0 := by
      intro U
      refine key_pp_FG2_dev τ q _ _ fun x₀ y₀ hfg => ?_
      have h := congrFun (hclass x₀ y₀ hfg .pp) U
      simp only [ite_true, Pi.zero_apply] at h
      have e1 : (∑ r, c (some .pp, r) * F (some .pp) r U) * dEps τ .pp (q + 1) x₀ y₀ =
          ∑ r, c (some .pp, r) * dEps τ .pp (q + 1) x₀ y₀ * F (some .pp) r U := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun r _ => by ring
      have e2 : (∑ r, c (none, r) * F none r U) * f5 τ q x₀ y₀ = ∑ r, c (none, r) * f5 τ q x₀ y₀ * F none r U := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [e1, e2]
      exact h
    have hA := Fintype.linearIndependent_iff.1 (hFi (some .pp)) (fun r => c (some .pp, r)) (by
      funext U
      simpa [Finset.sum_apply] using (hAB U).1)
    have hB := Fintype.linearIndependent_iff.1 (hFi none) (fun r => c (none, r)) (by
      funext U
      simpa [Finset.sum_apply] using (hAB U).2)
    exact fun r => ⟨hA r, hB r⟩
  rintro ⟨e, r⟩
  cases e with
  | none => exact (hpp r).2
  | some ε =>
    by_cases hε : ε = .pp
    · subst hε
      exact (hpp r).1
    · exact hsome ε hε r

/-- **Theorem C.T2(ii)**: "`For odd $N$, $\dim\ker H|_{S_z=+1/2}=2$. The kernel is spanned by`" the two states of
`g_{2m+1}` — the independence half: two independent `F ∈ Θ_2[(1,1)]` give two independent numerators (`N = 2m + 1`). -/
theorem explicit_odd_linearIndependent (τ : ℍ) (m : ℕ) (F : Fin 2 → ℂ → ℂ) (hF : ∀ r, F r ∈ Θ2 τ .pp)
    (hFi : LinearIndependent ℂ F) (f : Fin 2 → (Fin ((m + 1) + m) → ℂ) → ℂ)
    (hf : ∀ r, IsNumerator τ (m + 1) m (F r) (gOdd τ m) (f r)) : LinearIndependent ℂ f := by
  have _ := hF
  obtain ⟨x₀, y₀, hfg, hne⟩ := exists_FG2_gOdd_dev τ m
  exact li_of_numerators_dev τ (by omega) (gOdd τ m) (gOdd_G τ m).1 x₀ y₀ hfg hne F hFi f hf

/-- **Theorem C.T2(ii)**, `S_z = −½` ("`$S_z=-\tfrac12$ is the same with the species exchanged.`"): the independence half. -/
theorem explicit_oddSwap_linearIndependent (τ : ℍ) (m : ℕ) (F : Fin 2 → ℂ → ℂ) (hF : ∀ r, F r ∈ Θ2 τ .pp)
    (hFi : LinearIndependent ℂ F) (f : Fin 2 → (Fin (m + (m + 1)) → ℂ) → ℂ)
    (hf : ∀ r, IsNumerator τ m (m + 1) (F r) (gOddSwap τ m) (f r)) : LinearIndependent ℂ f := by
  have _ := hF
  obtain ⟨x₁, y₁, hfg, hne⟩ := exists_FG2_gOdd_dev τ m
  exact li_of_numerators_dev τ (by omega) (gOddSwap τ m) (fun x y c => (gOdd_G τ m).1 y x c) y₁ x₁
    (FG2_swap_dev τ hfg) hne F hFi f hf

end HRTorus.ZeroModes

end -- noncomputable section
