import tactic
import data.real.basic 
import data.complex.exponential 
import analysis.special_functions.pow

noncomputable theory
open_locale classical
 
open real

notation `|`x`|` := abs x

/-!
## p-GTFs

This is my speciality but it _needs_ integration, so this won't be able to be
filled in until somebody produces some sort of integration in lean or I prove it
out of spite for not having it.


I've actually remembered that we can define the πₚ function.
-/

def pip (p : ℝ) := (2 * pi)/ p * sin (pi / p)

-- def sinp (p : ℝ) := sorry

-- def cosp (p : ℝ) := sorry

