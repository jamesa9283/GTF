import tactic
import basic
import data.real.basic 
import data.complex.exponential

/-! 
# Defining the functions at zero

## Wonky Square GTFs

Let us show that these functions follow general trigonometric convention. We 
are going to show here that they have have values at 0 apart from cscₘ, but 
thats ∞ -/

noncomputable theory
open_locale classical
 
open real

lemma sinm_zero (m : ℕ): sinm 0 m = 0 :=
begin
  unfold sinm,
  rw sin_zero,
  rw zero_mul,
end

-- we know that p q > 0 because the negative values get funny and annoying.

lemma cosm_zero (m : ℕ) (hm : m ≠ 0) : cosm 0 m = 1 :=
begin
  unfold cosm,
  unfold radius,
  rw [cos_zero, one_mul, sin_zero, abs_zero, abs_one],
  rw zero_pow',
  norm_num,
  exact hm,
end

lemma tanm_zero (m : ℕ) : tanm 0 m = 0 :=
begin 
  unfold tanm,
  rw [sinm_zero, zero_div],
end

lemma secm_zero (m : ℕ) (hm : m ≠ 0) : secm 0 m = 1 :=
begin
  unfold secm,
  rw cosm_zero, 
  norm_num,
  exact hm,
end

/-!
## p-GTFs

-/

