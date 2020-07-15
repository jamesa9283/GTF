import tactic
import data.real.basic data.int.basic init.data.int.basic
import data.complex.exponential
import analysis.special_functions.trigonometric


-- local imports
 import basic zero_lemmas


open real

/- 033
Let us try to prove some stuff just about radius (x + y), just to make it easier tp rove 032
-/


lemma radius_add (a b m : ℝ) : radius (a + b) m = 1 / (|sin a * cos b + cos a * sin b| ^ m + |cos a * cos b - sin a * sin b| ^ m) ^ (1 / m) :=
begin
  unfold radius,
  rw [sin_add, cos_add],
  ---- rw pow_abs (sin a * cos b + cos a * sin b) m,
end

/- 031
Let us do the cosₘ x addition formula
-/

-- Thanks, I hate it.
lemma cosm_add ( x y m : ℝ) : cosm (x + y) m = (cos x * cos y - sin x * sin y) / (|cos x * cos y - sin x * sin y| ^ m + |sin x * cos y + cos x * sin y|^m)^ (1/m) :=
begin 
  unfold cosm,
  rw [radius_add, cos_add],
  simp,
  rw div_eq_inv_mul,
  rw [mul_comm, add_comm],
  -- nah, this is yuck. I think this is the most cursed thing in lean.
  -- it's worse.
  -- What have I proved: That this definition is just awful.
end

 -- that worked?!? No errors!

/- 032 
Now, for the sinₘ x one!
-/

lemma sinm_add (x y m : ℝ) : sinm (x + y) m = (sin x * cos y + cos x * sin y)/(|cos x * cos y - sin x * sin y|^m + |sin x * cos y + cos x * sin y|^m)^(1/m) :=
begin
  unfold sinm,
  rw [radius_add, sin_add],
  simp,
  rw div_eq_inv_mul,
  rw [mul_comm, add_comm],
end

/- 035

-/

lemma sinm_2x (x m : ℝ) : sinm (2*x) m = (2 * sin x * cos x) / (|(cos x) ^2 - (sin x) ^2| ^ m + |2 * sin x * cos x|^m)^ (1/m)  :=
begin
  rw [mul_comm, mul_two, sinm_add];
  repeat {rw [mul_comm, ←mul_two, ←pow_two, ←pow_two]},
  rw [mul_comm], rw mul_assoc, rw mul_comm (sin x) (cos x),
end

/- 036

-/

lemma cosm_2x (x m : ℝ) : cosm (2*x) m = ((cos x) ^ 2 - (sin x) ^ 2) / (|(cos x) ^2 - (sin x) ^2| ^ m + |2 * sin x * cos x|^m)^ (1/m)  :=
begin
  rw [mul_comm, mul_two, cosm_add];
  repeat {rw [←pow_two]},
  rw [mul_comm (sin x) (cos x), ←mul_two],
  rw [mul_comm (cos x) (sin x), mul_comm (sin x * cos x) 2, mul_assoc],
end

/- 036

-/

lemma sinm_sub (x m y : ℝ) : sinm (x - y) m = (sin x * cos y - cos x * sin y)/(|cos x * cos y + sin x * sin y|^m + |sin x * cos y - cos x * sin y|^m)^(1/m) :=
begin
  rw sub_eq_add_neg,
  rw [sinm_add x (-y), cos_neg, sin_neg],
  repeat {rw ←neg_mul_eq_mul_neg},
  rw [one_div_eq_inv, sub_neg_eq_add], 
  ring,
end

/- 039

-/

lemma cosm_sub (x m y : ℝ) : cosm (x - y) m = (cos x * cos y + sin x * sin y) / (|cos x * cos y + sin x * sin y| ^ m + |sin x * cos y - cos x * sin y|^m)^ (1/m) :=
begin
  rw sub_eq_add_neg,
  rw [cosm_add x (-y), cos_neg, sin_neg],
  repeat {rw ←neg_mul_eq_mul_neg},
  rw [one_div_eq_inv, sub_neg_eq_add], 
  ring,
end
