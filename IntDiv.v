Require Import Nat Arith Program.

Program Fixpoint divmod (a b: nat) (H: 0 < b) {measure a}: nat * nat :=
  match a <? b with
  | true  => (0, a)
  | false => let (q, r) := divmod (a-b) b H in (S q, r)
  end.
Next Obligation. clear divmod.
  rename Heq_anonymous into a_ge_b. symmetry in a_ge_b. apply Nat.ltb_ge in a_ge_b.
  apply (Nat.sub_lt _ _ a_ge_b H).
Qed.

Theorem division:
  forall (a b: nat), 0 < b -> exists! (q r: nat),
  0 <= r < b -> a = (q * b) + r.
Proof. Admitted.

