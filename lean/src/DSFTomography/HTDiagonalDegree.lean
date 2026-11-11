import DSFTomography.HTDiagonalMap
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Explicit total-degree bounds over the real coupling coordinates. The complex
matrix arithmetic is handled componentwise, before taking the measured real part. -/
noncomputable section
namespace DSFTomography.HT.Diagonal
open DSFTomography HT
variable {I : Type*}
def DegreeLE (n : ℕ) (f : V I → ℝ) : Prop :=
  ∃ P : MvPolynomial I ℝ, P.totalDegree ≤ n ∧ ∀ p, MvPolynomial.eval p P = f p

namespace DegreeLE
variable {m n : ℕ} {f g : V I → ℝ}
theorem const (r : ℝ) (n : ℕ) : DegreeLE n (fun _ : V I => r) :=
  ⟨.C r,by simp,by simp⟩
theorem coord (i : I) : DegreeLE 1 (fun p : V I => p i) :=
  ⟨.X i,by simp,by simp⟩
theorem mono (h : DegreeLE m f) (hm : m ≤ n) : DegreeLE n f :=
  let ⟨P,d,e⟩ := h; ⟨P,d.trans hm,e⟩
theorem add (h : DegreeLE n f) (k : DegreeLE n g) : DegreeLE n (fun p => f p + g p) := by
  obtain ⟨P,d,e⟩ := h; obtain ⟨Q,d',e'⟩ := k
  exact ⟨P+Q,(MvPolynomial.totalDegree_add _ _).trans (max_le d d'),by simp [e,e']⟩
theorem sub (h : DegreeLE n f) (k : DegreeLE n g) : DegreeLE n (fun p => f p - g p) := by
  obtain ⟨P,d,e⟩ := h; obtain ⟨Q,d',e'⟩ := k
  exact ⟨P-Q,(MvPolynomial.totalDegree_sub _ _).trans (max_le d d'),by simp [e,e']⟩
theorem mul (h : DegreeLE m f) (k : DegreeLE n g) : DegreeLE (m+n) (fun p => f p * g p) := by
  obtain ⟨P,d,e⟩ := h; obtain ⟨Q,d',e'⟩ := k
  exact ⟨P*Q,(MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add d d'),by simp [e,e']⟩
theorem cmul (c : ℝ) (h : DegreeLE n f) : DegreeLE n (fun p => c*f p) := by
  simpa using (const c 0).mul h
theorem sum {T : Type*} (s : Finset T) {f : T → V I → ℝ} (h : ∀ i ∈ s, DegreeLE n (f i)) :
    DegreeLE n (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (I := I) 0 n
  | insert i s hi ih =>
    simpa [hi] using (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))
end DegreeLE

private def Cdeg (n : ℕ) (f : V I → ℂ) :=
  DegreeLE n (fun p => (f p).re) ∧ DegreeLE n (fun p => (f p).im)
namespace Cdeg
variable {m n : ℕ} {f g : V I → ℂ}
private theorem const (z : ℂ) (n : ℕ) : Cdeg n (fun _ : V I => z) := ⟨.const _ _,.const _ _⟩
private theorem ofR {f : V I → ℝ} (h : DegreeLE n f) : Cdeg n (fun p => (f p : ℂ)) :=
  ⟨h,.const 0 n⟩
private theorem add (h : Cdeg n f) (k : Cdeg n g) : Cdeg n (fun p => f p+g p) :=
  ⟨h.1.add k.1,h.2.add k.2⟩
private theorem sub (h : Cdeg n f) (k : Cdeg n g) : Cdeg n (fun p => f p-g p) :=
  ⟨h.1.sub k.1,h.2.sub k.2⟩
private theorem mul (h : Cdeg m f) (k : Cdeg n g) : Cdeg (m+n) (fun p => f p*g p) :=
  ⟨(h.1.mul k.1).sub (h.2.mul k.2),(h.1.mul k.2).add (h.2.mul k.1)⟩
private theorem sum {T : Type*} (s : Finset T) {f : T → V I → ℂ} (h : ∀ i ∈ s, Cdeg n (f i)) :
    Cdeg n (fun p => ∑ i ∈ s, f i p) := by
  unfold Cdeg
  simp only [Complex.re_sum,Complex.im_sum]
  exact ⟨DegreeLE.sum _ (fun j hj => (h j hj).1),DegreeLE.sum _ (fun j hj => (h j hj).2)⟩
end Cdeg

private def MatrixDegree {T : Type*} (n : ℕ) (A : V I → Op T) := ∀ i j, Cdeg n (fun p => A p i j)
private theorem matMul {T : Type*} [Fintype T] {m n : ℕ} {A B : V I → Op T}
    (h : MatrixDegree m A) (k : MatrixDegree n B) : MatrixDegree (m+n) (fun p => A p * B p) :=
  fun i j => Cdeg.sum _ fun z _ => Cdeg.mul (h i z) (k z j)
private theorem matConst {T : Type*} (A : Op T) : MatrixDegree (I := I) 0 (fun _ => A) :=
  fun _ _ => Cdeg.const _ _
private theorem matBracket {T : Type*} [Fintype T] {m n : ℕ} {A B : V I → Op T}
    (h : MatrixDegree m A) (k : MatrixDegree n B) : MatrixDegree (m+n) (fun p => bracket (A p) (B p)) := by
  intro i j
  exact Cdeg.sub (matMul h k i j) (by simpa [Nat.add_comm] using matMul k h i j)

variable {S : Type*} [AddCommGroup S] [Fintype S] [DecidableEq S] (R : Bonds S)
omit [Fintype S] in
private theorem exchDegree (d : S) (a b : Axis) : DegreeLE 1 (fun p => exch R p d a b) := by
  unfold exch; split
  · apply DegreeLE.coord
  · apply DegreeLE.const

private theorem hamDegree : MatrixDegree 1 (ham R) := by
  intro i j
  simp only [ham,qubitH,realH,H,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Cdeg.add
  · apply Cdeg.sum; intro r _; apply Cdeg.sum; intro a _
    exact Cdeg.mul (Cdeg.ofR (.coord _)) (Cdeg.const _ 0)
  · repeat' (apply Cdeg.sum; intro _ _)
    exact Cdeg.mul (Cdeg.ofR (exchDegree R _ _ _)) (Cdeg.const _ 0)

private theorem avgTrace {n : ℕ} (A : S → Params R → Op (Config S)) (c : ℂ)
    (h : ∀ r, MatrixDegree n (A r)) :
    Cdeg n (fun p => avg (fun r => (A r p).trace * c)) := by
  change Cdeg n (fun p => (∑ r, (A r p).trace * c) / _)
  simp only [div_eq_mul_inv]
  apply Cdeg.mul (n := 0) _ (Cdeg.const _ 0)
  apply Cdeg.sum; intro r _
  apply Cdeg.mul (n := 0) _ (Cdeg.const _ 0)
  apply Cdeg.sum; intro i _
  exact h r i i

private theorem qtDegree (d : R.dirs) (u v : Axis) : DegreeLE 2 (fun p => qt R p d u v) := by
  let A := fun (r : S) (p : Params R) => ham R p * ham R p * (spin r u * spin (r+d.val) v)
  have h (r : S) : MatrixDegree 2 (A r) := matMul (matMul (hamDegree R) (hamDegree R)) (matConst _)
  simpa only [qt,quadraticCorrelation,div_eq_mul_inv,A] using (avgTrace R A _ h).1

private theorem onsiteDegree (a : Axis) : DegreeLE 2 (fun p => onsiteRow (ham R p) a) := by
  let A := fun (r : S) (p : Params R) => ham R p * bracket (bracket (spin r a) (ham R p)) (spin r a)
  have h (r : S) : MatrixDegree 2 (A r) :=
    matMul (hamDegree R) (matBracket (matBracket (matConst _) (hamDegree R)) (matConst _))
  simpa only [onsiteRow,div_eq_mul_inv,A,mul_neg,neg_mul] using
    (avgTrace R A (-(dim S)⁻¹) h).1

/-- A separate real polynomial in the physical coordinates for each measured
entry, with degree bound 1, 2 or 3 according to its moment indices. -/
theorem featureDegree (i : Index R) :
    DegreeLE (match i with | .inl _ => 2 | .inr (_,_,k) => k.val+1) (fun p => paperFeatures R p i) := by
  rw [paper_eq]
  cases i with
  | inl a => exact onsiteDegree R a
  | inr i =>
    obtain ⟨d,a,k⟩ := i
    have D := exchDegree R d
    have Q := qtDegree R d
    rcases (show k=0 ∨ k=1 ∨ k=2 by fin_cases k <;> decide) with rfl|rfl|rfl
    · simpa only [neg_one_mul] using (D a a).cmul (-1)
    · exact (((D _ _).mul (D _ _)).sub ((D _ _).mul (D _ _))).cmul (-8)
    · exact (((((D _ _).mul (Q _ _)).add ((D _ _).mul (Q _ _))).sub
        ((D _ _).mul (Q _ _))).sub ((D _ _).mul (Q _ _))).cmul 4
end DSFTomography.HT.Diagonal
