import tactic
import data.complex.exponential
import data.real.basic
import data.nat.basic

open nat real

example (n: ℕ) : exp 1 > (1 + 1/n)^n:=
begin
  induction n with d hd,
  {norm_num, 
   --suggest,
   sorry
  },
  {
      rw succ_eq_add_one,
      rw pow_succ,
      sorry
  },
end

example (n : ℕ) : exp 1 < (1 + 1/n)^(n+1) :=
begin 
  sorry
end

