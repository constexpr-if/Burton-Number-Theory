Require Import Nat Arith Program.

Program Fixpoint divmod (a b: nat) {measure a}: option (nat * nat) :=
  match b with
  | 0 => None
  | _ => match a <? b with
         | true  => Some (0, a)
         | false => match divmod (a-b) b with
                    | None => None
                    | Some (q, r) => Some (S q, r)
                    end
         end
  end.
Next Obligation.
  rename Heq_anonymous into le_b_a. rename n into b_not_0.
  symmetry in le_b_a. apply Nat.ltb_ge in le_b_a.
  destruct b. destruct b_not_0. reflexivity. clear b_not_0.
  apply (Nat.add_lt_mono_r _ _ (S b)). rewrite (Nat.sub_add _ _ le_b_a).
  apply Nat.lt_add_pos_r, Nat.lt_0_succ.
Qed.

Theorem division:
  forall (a b: nat), 0 < b -> exists! (q r: nat),
  0 <= r < b -> a = (q * b) + r.
Proof. Admitted.

