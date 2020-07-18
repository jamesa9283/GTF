import tactic
import data.real.basic data.int.basic init.data.int.basic
import data.complex.exponential
import analysis.special_functions.trigonometric


-- local imports
 import wonky_sq.basic


open real

/- 033
Let us try to prove some stuff just about radius (x + y), just to make it easier tp rove 032
-/


@[simp] lemma radius_add (a b m : ℝ) : radius (a + b) m = 1 / (|sin a * cos b + cos a * sin b| ^ m + |cos a * cos b - sin a * sin b| ^ m) ^ (1 / m) :=
begin
  unfold radius,
  rw [sin_add, cos_add],
  ---- rw pow_abs (sin a * cos b + cos a * sin b) m,
end

/- 031
Let us do the cosₘ x addition formula
-/

-- Thanks, I hate it.
@[simp] lemma cosm_add ( x y m : ℝ) : cosm (x + y) m = (cos x * cos y - sin x * sin y) / (|cos x * cos y - sin x * sin y| ^ m + |sin x * cos y + cos x * sin y|^m)^ (1/m) :=
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

@[simp] lemma sinm_add (x y m : ℝ) : sinm (x + y) m = (sin x * cos y + cos x * sin y)/(|cos x * cos y - sin x * sin y|^m + |sin x * cos y + cos x * sin y|^m)^(1/m) :=
begin
  unfold sinm,
  rw [radius_add, sin_add],
  simp,
  rw div_eq_inv_mul,
  rw [mul_comm, add_comm],
end

/- 035

-/

@[simp] lemma sinm_2x (x m : ℝ) : sinm (2*x) m = (2 * sin x * cos x) / (|(cos x) ^2 - (sin x) ^2| ^ m + |2 * sin x * cos x|^m)^ (1/m)  :=
begin
  rw [mul_comm, mul_two, sinm_add];
  repeat {rw [mul_comm, ←mul_two, ←pow_two, ←pow_two]},
  rw [mul_comm], rw mul_assoc, rw mul_comm (sin x) (cos x), 
end

/- 036

-/

@[simp] lemma cosm_2x (x m : ℝ) : cosm (2*x) m = ((cos x) ^ 2 - (sin x) ^ 2) / (|(cos x) ^2 - (sin x) ^2| ^ m + |2 * sin x * cos x|^m)^ (1/m)  :=
begin
  rw [mul_comm, mul_two, cosm_add];
  repeat {rw [←pow_two]},
  rw [mul_comm (sin x) (cos x), ←mul_two],
  rw [mul_comm (cos x) (sin x), mul_comm (sin x * cos x) 2, mul_assoc],
end

/- 036

-/

@[simp] lemma sinm_sub (x m y : ℝ) : sinm (x - y) m = (sin x * cos y - cos x * sin y)/(|cos x * cos y + sin x * sin y|^m + |sin x * cos y - cos x * sin y|^m)^(1/m) :=
begin
  rw sub_eq_add_neg,
  rw [sinm_add x (-y), cos_neg, sin_neg],
  repeat {rw ←neg_mul_eq_mul_neg},
  rw [one_div_eq_inv, sub_neg_eq_add], 
  ring,
end

/- 039

-/

@[simp] lemma cosm_sub (x m y : ℝ) : cosm (x - y) m = (cos x * cos y + sin x * sin y) / (|cos x * cos y + sin x * sin y| ^ m + |sin x * cos y - cos x * sin y|^m)^ (1/m) :=
begin
  rw sub_eq_add_neg,
  rw [cosm_add x (-y), cos_neg, sin_neg],
  repeat {rw ←neg_mul_eq_mul_neg},
  rw [one_div_eq_inv, sub_neg_eq_add], 
  ring,
end

/- 043

-/

@[simp] lemma cosm_sq_plus_sinm_sq (x m : ℝ) : cosm x m ^ 2 + sinm x m ^ 2 = radius x m ^ 2 :=
begin
  unfold sinm cosm,
  ring,
  rw [mul_comm (sin x ^2), ←mul_add (radius x m ^2) (cos x ^ 2) (sin x ^2), add_comm, sin_sq_add_cos_sq x, mul_one],
end

/- 045

-/

@[simp] lemma radius_nonneg (x m : ℝ) : 0 ≤ radius x m :=
begin
  unfold radius,
  ring,
  rw inv_nonneg,
  rw ←inv_eq_one_div,
  apply rpow_nonneg_of_nonneg,
  apply add_nonneg,
  repeat {apply rpow_nonneg_of_nonneg, apply abs_nonneg},
end

@[simp] lemma abs_radius_eq_radius (x m : ℝ) (H: 0 ≤ radius x m): |radius x m| = radius x m := abs_of_nonneg H


lemma cos_zero_im_sin_one (x : ℝ) (F : 0 ≤ sin x) : cos x = 0 → sin x = 1 :=
begin
   have H : sin x ^ 2 + cos x ^2 = 1,
   {rw sin_sq_add_cos_sq},
  intros,
  {
    rw a at H, 
    norm_num at H,
    apply_fun sqrt at H,
    rw sqrt_sqr at H,
    rw sqrt_one at H,
    rw H,
    exact F,
  },
end

/- 044

-/

lemma cosm_powm_plus_sinm_powm (m n x : ℝ) (H : m ≠ 0) (F : 0 ≤ sin x) : |sinm x m|^m + |cosm x m|^m = 1 :=
begin
  unfold sinm cosm,
  repeat {rw [abs_mul, mul_rpow]},
  repeat{apply abs_nonneg,},
  --have H : radius_nonneg,
  rw abs_radius_eq_radius,
  rw ←add_mul,
  rw radius_powm m x m,
  rw ←div_eq_mul_one_div,
  rw div_self,
  {
    -- this looks like hell
    by_cases h : cos x = 0,
    {
      have fs : |sin x| = 1,
      {
        have f := sin_sq_add_cos_sq x,
        rw [h] at f,
        norm_num at f,
        apply_fun sqrt at f,
        rw [sqrt_sqr_eq_abs, sqrt_one] at f,
        exact f,
      },
      {
        rw [h, fs, abs_zero, zero_rpow],
        norm_num,
        exact H,
      },
    },
    {
      have hcpos : 0 < | cos x | ^ m := rpow_pos_of_pos (abs_pos_of_ne_zero h) _,
      have hsnn : 0 ≤ | sin x | ^ m := rpow_nonneg_of_nonneg (abs_nonneg _) _,
      linarith,
    },
  },
  {exact H},
  {apply radius_nonneg},
end
