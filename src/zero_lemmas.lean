import tactic
import basic
import data.real.basic 
import data.complex.exponential 
import analysis.special_functions.pow

/-! 
# Defining the functions at zero

## Wonky Square GTFs

Let us show that these functions follow general trigonometric convention. We 
are going to show here that they have have values at 0 apart from cscₘ, but 
thats ∞ -/

noncomputable theory
open_locale classical
 
open real

/- 008 
Here we prove that sinₘ 0 = 0.
-/
lemma sinm_zero (m : ℝ): sinm 0 m = 0 :=
begin
  unfold sinm,
  rw sin_zero,
  rw zero_mul,
end

-- we know that p q > 0 because the negative values get funny and annoying.

-- #print instances has_pow

/- 009
Here we prove a lemma similar to 008, but for cosₘ
-/
lemma cosm_zero (m : ℝ) (hm : m ≠ 0) : cosm 0 m = 1 :=
begin
  unfold cosm,
  unfold radius,
  rw [cos_zero, one_mul, sin_zero, abs_zero, abs_one],
  simp,
  rw [zero_rpow, zero_add, one_rpow],
  simp, exact hm,
  end 

/- 010 
Similar to 008, but for tanₘ
-/
lemma tanm_zero (m : ℝ) : tanm 0 m = 0 :=
begin 
  unfold tanm,
  rw [sinm_zero, zero_div],
end

/- 011
Similar to 008, but for secₘ
-/
lemma secm_zero (m : ℝ) (hm : m ≠ 0) : secm 0 m = 1 :=
begin
  unfold secm,
  rw cosm_zero, 
  norm_num,
  exact hm,
end

/-!
## p-GTFs
nothing yet
-/

