import Chess.Parsing

namespace Chess
namespace Parsing

open Chess

theorem natDigitValue_digitChar_of_lt10 (d : Nat) (hd : d < 10) :
    natDigitValue (Nat.digitChar d) = d := by
  let f : Fin 10 := ⟨d, hd⟩
  have hAll : ∀ x : Fin 10, natDigitValue (Nat.digitChar x.val) = x.val := by
    native_decide
  simpa [f] using hAll f

theorem digitChar_isDigit_of_lt10 (d : Nat) (hd : d < 10) : (Nat.digitChar d).isDigit = true := by
  let f : Fin 10 := ⟨d, hd⟩
  have hAll : ∀ x : Fin 10, (Nat.digitChar x.val).isDigit = true := by
    native_decide
  simpa [f] using hAll f

theorem natFromDigitChars_toDigitsCore (fuel n : Nat) (ds : List Char)
    (h : n + 1 ≤ fuel) :
    natFromDigitChars (Nat.toDigitsCore 10 fuel n ds) =
      n * 10 ^ ds.length + natFromDigitChars ds := by
  induction fuel generalizing n ds with
  | zero =>
      cases Nat.not_succ_le_zero n h
  | succ fuel ih =>
      have hFuel : n ≤ fuel := by
        -- `n+1 ≤ fuel+1` implies `n ≤ fuel`.
        have : Nat.succ n ≤ Nat.succ fuel := by
          simpa [Nat.succ_eq_add_one] using h
        exact (Nat.succ_le_succ_iff).1 this
      -- The core function branches on whether `n / 10 = 0`.
      by_cases hdiv : n / 10 = 0
      ·
        have hlt : n < 10 := Nat.lt_of_div_eq_zero (by decide : 0 < (10 : Nat)) hdiv
        have hmod : n % 10 = n := Nat.mod_eq_of_lt hlt
        have hd : natDigitValue (Nat.digitChar (n % 10)) = n := by
          -- `n % 10 = n`, and `n < 10`.
          simpa [hmod] using natDigitValue_digitChar_of_lt10 n hlt
        simp [Nat.toDigitsCore, hdiv, natFromDigitChars, hd, Nat.mul_assoc, Nat.mul_add, Nat.add_assoc]
      ·
        have hnpos : 0 < n := by
          cases n with
          | zero =>
              simp at hdiv
          | succ n =>
              exact Nat.succ_pos _
        have hdivlt : n / 10 < n :=
          Nat.div_lt_self hnpos (by decide : 1 < (10 : Nat))
        have hdivLe : n / 10 + 1 ≤ n := Nat.succ_le_of_lt hdivlt
        have hRec : n / 10 + 1 ≤ fuel := Nat.le_trans hdivLe hFuel
        have ih' :=
          ih (n := n / 10) (ds := Nat.digitChar (n % 10) :: ds) hRec
        have hdVal :
            natDigitValue (Nat.digitChar (n % 10)) = n % 10 := by
          have hmodLt : n % 10 < 10 := Nat.mod_lt n (by decide : 0 < (10 : Nat))
          simpa using natDigitValue_digitChar_of_lt10 (n % 10) hmodLt
        -- Use the induction hypothesis after simplifying the `toDigitsCore` branch.
        have hStep :
            natFromDigitChars (Nat.toDigitsCore 10 (fuel + 1) n ds) =
              n / 10 * 10 ^ (ds.length + 1) +
                natDigitValue (Nat.digitChar (n % 10)) * 10 ^ ds.length +
                natFromDigitChars ds := by
          -- `simp` reduces the recursive call to the smaller-fuel computation.
          -- Then `ih'` provides the value formula for that call.
          simpa [Nat.toDigitsCore, hdiv, natFromDigitChars, List.length_cons, Nat.pow_succ, Nat.mul_assoc,
            Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih'
        -- Massage into the target `n * 10^|ds| + ...` using `Nat.div_add_mod`.
        have hDivMod : n / 10 * 10 + n % 10 = n := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm,
            Nat.mul_assoc] using (Nat.div_add_mod n 10)
        -- Finish with arithmetic normalization.
        have hk : 10 ^ (ds.length + 1) = 10 ^ ds.length * 10 := by
          simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        -- Rewrite the step result into a common-factor form.
        have hStep' :
            natFromDigitChars (Nat.toDigitsCore 10 (fuel + 1) n ds) =
              (n / 10 * 10 + n % 10) * 10 ^ ds.length + natFromDigitChars ds := by
          -- Start from `hStep` and rewrite `digitChar` value + the `pow` exponent.
          calc
            natFromDigitChars (Nat.toDigitsCore 10 (fuel + 1) n ds)
                = n / 10 * 10 ^ (ds.length + 1) +
                    natDigitValue (Nat.digitChar (n % 10)) * 10 ^ ds.length +
                    natFromDigitChars ds := hStep
            _ = n / 10 * (10 ^ ds.length * 10) +
                    natDigitValue (Nat.digitChar (n % 10)) * 10 ^ ds.length +
                    natFromDigitChars ds := by
                  simp [hk, Nat.mul_assoc]
            _ = (n / 10 * 10) * 10 ^ ds.length +
                    natDigitValue (Nat.digitChar (n % 10)) * 10 ^ ds.length +
                    natFromDigitChars ds := by
                  simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
            _ = (n / 10 * 10 + natDigitValue (Nat.digitChar (n % 10))) * 10 ^ ds.length +
                    natFromDigitChars ds := by
                  simp [Nat.add_mul, Nat.add_assoc, Nat.mul_assoc]
            _ = (n / 10 * 10 + n % 10) * 10 ^ ds.length +
                    natFromDigitChars ds := by
                  simp [hdVal]
        -- Now use `div_add_mod` to replace the parenthesized sum with `n`.
        simpa [hDivMod, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStep'

theorem natFromDigitChars_toDigits (n : Nat) :
    natFromDigitChars (Nat.toDigits 10 n) = n := by
  -- `Nat.toDigits 10 n = Nat.toDigitsCore 10 (n+1) n []`.
  simpa [Nat.toDigits, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero] using
    (natFromDigitChars_toDigitsCore (fuel := n + 1) (n := n) (ds := []) (by simp))

theorem toDigits_all_isDigit (n : Nat) : (Nat.toDigits 10 n).all Char.isDigit = true := by
  -- Stronger helper for `toDigitsCore` with an `all` invariant.
  have hCore :
      ∀ fuel n ds,
        (ds.all Char.isDigit = true) →
          (Nat.toDigitsCore 10 fuel n ds).all Char.isDigit = true := by
    intro fuel n ds hds
    induction fuel generalizing n ds with
    | zero =>
        simpa [Nat.toDigitsCore] using hds
    | succ fuel ih =>
        by_cases hdiv : n / 10 = 0
        ·
          have hlt : n < 10 := Nat.lt_of_div_eq_zero (by decide : 0 < (10 : Nat)) hdiv
          have hmodLt : n % 10 < 10 := by
            simpa [Nat.mod_eq_of_lt hlt] using hlt
          have hdDigit : (Nat.digitChar (n % 10)).isDigit = true :=
            digitChar_isDigit_of_lt10 (n % 10) hmodLt
          simp [Nat.toDigitsCore, hdiv, hds, hdDigit]
        ·
          have hmodLt : n % 10 < 10 := Nat.mod_lt n (by decide : 0 < (10 : Nat))
          have hdDigit : (Nat.digitChar (n % 10)).isDigit = true :=
            digitChar_isDigit_of_lt10 (n % 10) hmodLt
          have hds' : ((Nat.digitChar (n % 10)) :: ds).all Char.isDigit = true := by
            simp [hds, hdDigit]
          simpa [Nat.toDigitsCore, hdiv, hds', hdDigit] using
            (ih (n := n / 10) (ds := (Nat.digitChar (n % 10)) :: ds) hds')
  simpa [Nat.toDigits] using hCore (fuel := n + 1) (n := n) (ds := []) (by simp)

theorem stringToNatDigits?_toString (n : Nat) : stringToNatDigits? (toString n) = some n := by
  change stringToNatDigits? (Nat.repr n) = some n
  -- Unfold the representation into digit characters.
  cases hDigits : Nat.toDigits 10 n with
  | nil =>
      -- Contradiction: `natFromDigitChars (toDigits 10 n) = n`.
      have : natFromDigitChars (Nat.toDigits 10 n) = 0 := by
        simp [hDigits, natFromDigitChars]
      have hVal : natFromDigitChars (Nat.toDigits 10 n) = n := natFromDigitChars_toDigits n
      have hn : n = 0 := by simpa [this] using hVal.symm
      subst hn
      have h0 : Nat.toDigits 10 0 ≠ [] := by
        native_decide
      cases (h0 hDigits)
  | cons d ds =>
      have hAll : (d :: ds).all Char.isDigit = true := by
        simpa [hDigits] using toDigits_all_isDigit n
      have hVal : natFromDigitChars (d :: ds) = n := by
        simpa [hDigits] using natFromDigitChars_toDigits n
      -- Reduce `stringToNatDigits?` to the `toDigits` list.
      simp [stringToNatDigits?, Nat.repr, hDigits, hAll, hVal]

theorem parseNatField_toString_roundtrip (n : Nat) (label : String) :
    parseNatField (toString n) label = .ok n := by
  simp [parseNatField, stringToNatDigits?_toString]

end Parsing
end Chess
