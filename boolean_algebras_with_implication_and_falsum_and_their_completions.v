(** This code compiles succesfully with Coq8.9

We define boolean and complete boolean algebra using
the implication operation and the "false" constant (and the inf/forall operator
for the complete case)
Later in the text all algebraic relationships that prove the objects involved
are actually boolean algebras are proven, namely that these define 
Heyting algebras where the negation operator is involutive.

The transformation of any peordered set into a complete boolean algebra
andthe introduction of an icreasing map (which turns out to be injective when
the preordered set is a boolean algebra itself, giving the notion of 
the completion of a boolean algebra) between them are also discussed 

The order in which the concepts are presented may seem very strange at first 
sight but this is because, since the objects involved are very polymorphic
 (at least the way they are implemented there but I wonder if there are other
ways to avoid this fact), inconsistencies in universes arise.
*)

Section Boolean_algebra_definition.

  Polymorphic Cumulative Record boolean_algebra:=
    make_ba{
        ba_domain: Type;
        ba_implies: ba_domain -> ba_domain -> ba_domain;
        ba_false: ba_domain;
        ba_equivalence: ba_domain -> ba_domain -> Type;
        ba_reflexivity: forall x:ba_domain, ba_equivalence x x;
        ba_symmetry_and_transitivity:
          forall x y z:ba_domain,
            ba_equivalence x y -> ba_equivalence x z -> ba_equivalence y z;
        ba_compatibility: forall x x' y y':ba_domain,
            ba_equivalence x x' -> ba_equivalence y y' ->
            ba_equivalence (ba_implies x y) (ba_implies x' y');
        ba_axiom_1: forall x y z: ba_domain,
            ba_equivalence
              (ba_implies ba_false z)
              (ba_implies x (ba_implies y x));
        ba_axiom_2: forall x y z: ba_domain,
            ba_equivalence
              (ba_implies x (ba_implies y z))
              (ba_implies (ba_implies x y) (ba_implies x z));
        ba_peirce: forall x y:ba_domain,
            ba_equivalence (ba_implies (ba_implies x y) x) x;
        ba_implicative_or: forall x y:ba_domain,
            ba_equivalence
              (ba_implies (ba_implies x y) y) (ba_implies (ba_implies y x) x) 
      }.

End Boolean_algebra_definition.

Section Complete_boolean_algebra_definition.

  Polymorphic Cumulative Record complete_boolean_algebra:=
    make_cba{
        cba_domain: Type;
        cba_implies: cba_domain -> cba_domain -> cba_domain;
        cba_false: cba_domain;
        cba_all: forall J: Type, (J -> cba_domain) -> cba_domain;
        cba_equivalence: cba_domain -> cba_domain -> Type;
        cba_reflexivity: forall x: cba_domain, cba_equivalence x x;
        cba_symmetry_and_transitivity:
          forall x y z:cba_domain,
            cba_equivalence x y -> cba_equivalence x z -> cba_equivalence y z;
        cba_compatibility: forall x x' y y':cba_domain,
            cba_equivalence x x' -> cba_equivalence y y' ->
            cba_equivalence (cba_implies x y) (cba_implies x' y');
        cba_axiom_1: forall x y z: cba_domain,
            cba_equivalence
              (cba_implies cba_false z)
              (cba_implies x (cba_implies y x));
        cba_axiom_2: forall x y z: cba_domain,
            cba_equivalence
              (cba_implies x (cba_implies y z))
              (cba_implies (cba_implies x y) (cba_implies x z));
        cba_peirce: forall x y:cba_domain,
            cba_equivalence (cba_implies (cba_implies x y) x) x;
        cba_implicative_or: forall x y:cba_domain,
            cba_equivalence
              (cba_implies (cba_implies x y) y) (cba_implies (cba_implies y x) x); 
        cba_all_inf: forall (x: cba_domain) (J:Type) (f: J -> cba_domain),
            prod
              ((cba_equivalence (cba_implies cba_false cba_false)
                                (cba_implies x (cba_all J f)))
               ->
               (forall (j: J),
                   cba_equivalence (cba_implies cba_false cba_false)
                                   (cba_implies x (f j))))
              ((forall (j: J),
                   cba_equivalence (cba_implies cba_false cba_false)
                                   (cba_implies x (f j)))
               ->
               (cba_equivalence (cba_implies cba_false cba_false)
                                (cba_implies x (cba_all J f))))
      }.

End Complete_boolean_algebra_definition.

Section a_propositional_proof_system.

  Section type_valued_list_membership.

    Variable T: Type.
    Variable m:T.

    Inductive type_valued_list_member: list T -> Type:=
    |tvlm_head: forall l:list T, type_valued_list_member (cons m l)
    |tvlm_tail: forall (h: T) (t: list T),
        type_valued_list_member t -> type_valued_list_member (cons h t).      
    
  End type_valued_list_membership.

  Variable V:Type.

  Inductive propositional_formula: Type:=
  |pf_var: V -> propositional_formula
  |pf_false: propositional_formula
  |pf_implies: propositional_formula -> propositional_formula -> propositional_formula.

  Notation P:= propositional_formula.
  Notation "a § b":= (pf_implies a b) (right associativity, at level 51).
  Notation f:= pf_false.

  Section interpreter.

    Variable B: Type.
    Variable b_impl: B -> B -> B.
    Variable b_f: B.
    Variable environment: V -> B.

    Fixpoint prop_interpreter (x: P) {struct x}: B:=
      match x with
      |pf_var v => environment v
      |pf_false => b_f
      |pf_implies y z => b_impl (prop_interpreter y) (prop_interpreter z)
      end.
    
  End interpreter.
  
  Section Hilbert_system.

    Variable l: list (propositional_formula).
    
    Inductive pf_hilbert_system_proof:P -> Type:=
    |pfhs_ax: forall (m: P), type_valued_list_member P m l -> pf_hilbert_system_proof m
    |pfhs_k: forall x y:P, pf_hilbert_system_proof (x § y § x)
    |pfhs_s: forall x y z:P, pf_hilbert_system_proof ((x § y § z) § (x § y) § x § z)
    |pfhs_absurd: forall x: P, pf_hilbert_system_proof (((x § f) § f) § x)
    |pfhs_mp: forall x y:P, pf_hilbert_system_proof (x § y) ->
                            pf_hilbert_system_proof x -> pf_hilbert_system_proof y.

    Definition pfhs_i (x: P): pf_hilbert_system_proof (x § x).
    Proof.
      apply (pfhs_mp (x § x § x)). apply (pfhs_mp (x § (x § x) § x)). apply pfhs_s.
      apply pfhs_k. apply pfhs_k.
    Defined.
    
    Definition pfhs_implies_weakening (a b:P):
      pf_hilbert_system_proof a -> pf_hilbert_system_proof (b § a).
    Proof.
      intros J. apply (pfhs_mp a). apply pfhs_k. apply J.
    Defined.
    
  End Hilbert_system.

  Notation "l |- a":= (pf_hilbert_system_proof l a) (at level 52).
  
  Fixpoint pfhs_deduction_theorem (t: list P) (h a: P) (pr: (cons h t) |- a) {struct pr}:
    t |- h § a.
  Proof.
    destruct pr. inversion t0. apply pfhs_i. apply pfhs_mp with (x:= m). apply pfhs_k.
    apply pfhs_ax; assumption. 
    apply pfhs_implies_weakening; apply pfhs_k.
    apply pfhs_implies_weakening; apply pfhs_s.
    apply pfhs_implies_weakening; apply pfhs_absurd.
    apply (pfhs_mp t (h § x)). apply (pfhs_mp t (h § x § y)). apply pfhs_s.
    apply pfhs_deduction_theorem; assumption. apply pfhs_deduction_theorem; assumption.
  Defined.

  Fixpoint pfhs_weakening
           (t u: list P)
           (incl: forall m: P, type_valued_list_member P m t ->
                               type_valued_list_member P m u)
           (a: P) (pr: t |- a) {struct pr}: u |- a.
  Proof.
    destruct pr. apply pfhs_ax; apply incl; assumption.
    apply pfhs_k. apply pfhs_s. apply pfhs_absurd.
    apply (pfhs_mp u x); apply (pfhs_weakening t); assumption.
  Defined.

  Definition pfhs_head_weakening (t: list P) (h a:P): t |- a -> cons h t |- a.
  Proof.
    apply pfhs_weakening; intro m;  apply tvlm_tail.
  Defined.

  Ltac ded:= apply pfhs_deduction_theorem.
  Ltac we:= apply pfhs_weakening.
  Ltac ax:= apply pfhs_ax.
  Ltac mp u:= apply pfhs_mp with (x := u).
  Ltac hm:= apply tvlm_head.
  Ltac tm:= apply tvlm_tail.
  Ltac ka:= apply pfhs_k.
  Ltac sa:= apply pfhs_s.
  Ltac ia:= apply pfhs_i.
  Ltac aa:= apply pfhs_absurd.
  Ltac hwe:= apply pfhs_head_weakening.
  Ltac iwe:= apply pfhs_implies_weakening.
  
  Definition pfhs_double_negation (l: list P) (x: P): l |- (x § f) § f -> l |- x.
  Proof.
    apply pfhs_mp; aa.
  Defined.

  Ltac dn:= apply pfhs_double_negation.

  Definition pfhs_syllogism (l: list P) (x y z:P): l |- x § y -> l|- y § z -> l |- x § z.
  Proof.
    intros M N. mp (x § y). mp (x § (y § z)). sa. iwe; apply N. apply M.
  Defined.

  Ltac syl p:= apply pfhs_syllogism with (y:= p).

  Definition pfhs_polarity (l: list P) (x x' y y':P):
    l |- x' § x -> l |- y § y' -> l |- (x § y) § (x' § y').
  Proof.
    intros A B. ded; ded. mp y. hwe; hwe; apply B. mp x. ax; tm; hm. mp x'.
    hwe; hwe; apply A. ax; hm.
  Defined.

  Definition pfhs_polarity_formula (l: list P) (x x' y y':P):
    l |- (x' § x) § (y § y') § (x § y) § (x' § y').
  Proof.
    ded; ded; apply pfhs_polarity. ax; tm; hm. ax; hm.
  Defined.  
  
  Definition pfhs_explosion (l: list P) (x: P): l |- f § x.
  Proof.
    ded. dn. mp f. ka. ax; hm.
  Defined.

  Ltac expl:= apply pfhs_explosion.

  Definition pfhs_b (l: list P) (x y z:P): l |- (y § z) § (x § y) § (x § z).
  Proof.
    syl (x § y § z). ka. sa.
  Defined.    
    
  Definition pfhs_peirce (l: list P) (x y:P): l |- ((x § y) § x) § x.
  Proof.
    ded. dn. ded. mp x. ax; hm. mp (x § y). ax; tm; hm. syl f. ax; hm. expl.
  Defined.

  Definition pfhs_implies_or_permutation (l: list P)(x y:P):l |- ((x § y) § y) § (y § x) § x.
  Proof.
    ded; ded. mp ((x § y) § x). apply pfhs_peirce. syl y. ax; tm; hm. ax; hm.
  Defined.

  Definition pf_and (x y:P):P:= (x § y § f) § f.

  Definition pfhs_and_intro (l: list P) (x y:P): l |- x § y § (pf_and x y).
  Proof.
    ded; ded; ded. mp y. mp x. ax; hm. ax; tm; tm; hm. ax; tm; hm.
  Defined.

  Definition pfhs_and_left_elim (l: list P) (x y:P): l |- (pf_and x y) § x.
  Proof.
    ded. dn. ded. mp (x § y § f). ax; tm; hm. ded; ded; mp x. ax; tm; tm; hm. ax; tm; hm.
  Defined.

  Definition pfhs_and_right_elim (l: list P) (x y: P): l |- (pf_and x y) § y.
  Proof.
    ded. dn. ded. mp (x § y § f). ax; tm; hm. iwe; ax; hm.
  Defined.

  Definition pfhs_heyting_left (l: list P) (x y z:P):
    l|- ((pf_and x y) § z) § x § y § z.
  Proof.
    ded; ded; ded; mp (pf_and x y). ax; tm; tm; hm. mp y. mp x. apply pfhs_and_intro.
    ax; tm; hm. ax; hm.
  Defined.

  Definition pfhs_heyting_right (l: list P) (x y z:P):
    l|-  (x § y § z) § (pf_and x y) § z.
  Proof.
    ded; ded. mp y. mp x. ax; tm; hm. mp (pf_and x y). apply pfhs_and_left_elim. ax; hm.
    mp (pf_and x y). apply pfhs_and_right_elim. ax; hm.
  Defined.

  Notation pfhs_eq:=(fun (l:list P) (a b: P) => prod (l |- a § b) (l |- b § a)).

  Definition pfhs_eq_s: forall (l: list P) (x y z:P),
      pfhs_eq l (x § y § z) ((x § y) § x § z).
  Proof.
    intros; split. sa. ded; ded; ded. mp x. mp (x § y). ax; tm; tm; hm. iwe; ax; hm.
    ax; tm; hm.
  Defined.       

  Definition pfhs_eq_k_explosion (l: list P) (x y z:P):
    pfhs_eq l (f § z) (y § x § y).
  Proof.
    split. iwe; ka. iwe; expl.
  Defined.

  Definition pfhs_eq_peirce (l: list P) (x y:P):
    pfhs_eq l ((x § y) § x) x.
  Proof.
    split. apply pfhs_peirce. ka.
  Defined.

  Definition pfhs_eq_implies_or_permutation (l: list P) (x y:P):
    pfhs_eq l ((x § y) § y) ((y § x) § x).
  Proof.
    split; apply pfhs_implies_or_permutation.
  Defined.
  
  Definition pfhs_eq_heyting (l: list P) (x y z:P):
    pfhs_eq l ((pf_and x y) § z) (x § y § z).
  Proof.
    split. apply pfhs_heyting_left. apply pfhs_heyting_right.
  Defined.
  
  Definition pf_or (a b:P):P:= (a § f) § b.

  Definition pfhs_or_left_intro (l: list P) (x y:P): l |- x § (pf_or x y).
  Proof.
    ded. ded. mp f. expl. mp x. ax; hm. ax; tm; hm.
  Defined.

  Definition pfhs_or_right_intro (l: list P) (x y:P): l |- y § (pf_or x y).
  Proof.
    ka. 
  Defined.

  Definition pfhs_or_elim (l: list P) (x y z:P):
    l|- (x § z) § (y § z) § (pf_or x y) § z.
  Proof.
    ded; ded; ded. dn. ded. mp z. ax; hm. mp (x § f). syl y. ax; tm; hm.
    ax; tm; tm; hm. syl z. ax; tm; tm; tm; hm. ax; hm.
  Defined.      

  Definition pfhs_practical_or_elim (l: list P) (x y z:P):
    l |- pf_or x y -> cons x l |- z -> cons y l |- z -> l |- z.
  Proof.
    intros A B C. mp (pf_or x y). mp (y § z). mp (x § z). apply pfhs_or_elim. ded; apply B.
    ded; apply C. apply A.
  Defined.
  
  Definition pfhs_eq_or_equivalence (l: list P) (x y:P):
    pfhs_eq l (pf_or x y) ((x § y) § y).
  Proof.
    split. ded. apply (pfhs_practical_or_elim (cons (pf_or x y) l) x y). ax; hm.
    ded; mp x. ax; hm. ax; tm; hm. mp y. ka. ax; hm. ded. ded. mp (x § y). ax; tm; hm.
    ded. mp f. expl. mp x. ax; tm; hm. ax; hm.
  Defined.       
  
End a_propositional_proof_system.

(** Examples and general_constructions *)

Section single_bits.  
    
  Definition two_valued_boolean_algebra: boolean_algebra.
  Proof.
    apply (make_ba bool implb false (fun x y: bool => x = y)). intros; apply eq_refl.
    intros x y z e f; rewrite <- e; assumption. intros x x' y y' e f.
    rewrite e; rewrite f;  destruct x'; destruct y'; simpl; apply eq_refl.
    intros x y z; destruct x; destruct y; destruct z; simpl; apply eq_refl.
    intros x y z; destruct x; destruct y; destruct z; simpl; apply eq_refl.
    intros x y; destruct x; destruct y; simpl; apply eq_refl.
    intros x y; destruct x; destruct y; simpl; apply eq_refl.    
  Defined.
  
End single_bits.

Section regular_formulas.

  Notation RProp:= {p: Prop | (~~ p) -> p}.

  Definition rp_false: RProp.
  Proof.
    exists False. intro F; apply F; intro G; apply G.
  Defined.

  Definition rp_implies (a b:RProp): RProp.
  Proof.
    exists ((proj1_sig a) -> (proj1_sig b)). intros F G. apply (proj2_sig b).
    intro K. apply F. intro L. apply (K (L G)).
  Defined.

  Definition rp_all (T: Type) (f: T -> RProp): RProp.
  Proof.
    exists (forall t: T, proj1_sig (f t)). intro F1. intro t. apply (proj2_sig (f t)).
    intro F2. apply F1. intro F3. apply (F2 (F3 t)).
  Defined.    

  Definition rp_equivalence (x y: RProp):= proj1_sig x <-> proj1_sig y.

  Lemma equiv_tauto_false: forall A B:Prop, A -> ((False -> B) <-> A).
  Proof.
    intros A B p. split. intros; assumption. intro q; apply False_rect.
  Defined.
  
  Definition Regular_Prop: complete_boolean_algebra.
  Proof.
    apply (make_cba RProp rp_implies rp_false rp_all rp_equivalence).
    intros; destruct x; simpl; apply iff_refl.
    intros x y z; destruct x as (px, rx); destruct y as (py, ry); destruct z as (pz, rz).
    unfold rp_equivalence. simpl. intros. apply iff_trans with (B:= px).
    apply iff_sym; assumption. assumption. intros x y a b.
    destruct x as (x,rx); destruct y as (y,ry); destruct a as (a,ra); destruct b as (b,rb).
    unfold rp_equivalence. simpl; intros A B. apply iff_trans with (B:= x -> b).
    apply imp_iff_compat_l; assumption. apply imp_iff_compat_r; assumption.
    intros x y z; unfold rp_equivalence; simpl. apply equiv_tauto_false.
    intros; assumption. intros x y z; unfold rp_equivalence; simpl.
    split. intros A B C. apply (A C (B C)). intros A B C. apply A.
    intro; assumption. assumption. 
    intros x y; destruct x as (a, pa); destruct y as (b, pb); unfold rp_equivalence; simpl.
    split. intro A; apply pa. intro F; apply F. apply A. intro B; contradiction.
    intros; assumption. intros. unfold rp_equivalence; simpl; split.
    intros A B; apply (proj2_sig x); intro F; apply F; apply B; apply A; intro; contradiction.
    intros A B; apply (proj2_sig y); intro F; apply F; apply B; apply A; intro; contradiction.
    intros x J f; unfold rp_equivalence; simpl; split; split; intros P Q.
    apply H. intros; assumption. apply Q. apply Q. intro t; apply H. intros; assumption.
    assumption. assumption.
  Defined.  
    
End regular_formulas.

Section Lindenbaum_algebras.

  Variable P:Type.
  Variable p_impl:  P -> P -> P.
  Variable p_f: P.

  Variable proof_system: P -> Type.

  Notation "x -o y":= (p_impl x y) (right associativity, at level 43).
  Notation f:= p_f.
  Notation "|- x":= (proof_system x) (at level 44).

  Variable ps_k: forall x y:P, |- x -o y -o x.
  Variable ps_s: forall x y z:P, |- (x -o y -o z) -o (x -o y) -o x -o z.
  Variable ps_a: forall x: P, |- ((x -o f) -o f) -o x.
  Variable ps_mp: forall x y:P, |- x -o y -> |- x -> |- y.

  Notation intp:= ((fun (V:Type) (env: V -> P) =>
                      prop_interpreter V P p_impl p_f env)).

  Fixpoint prop_soundness
           (V: Type) (env: V -> P) (l: list (propositional_formula V))
           (A: forall u: propositional_formula V,
               type_valued_list_member (propositional_formula V) u l -> |- (intp V env u))
           (x: propositional_formula V) (pr: pf_hilbert_system_proof V l x) {struct pr}:
  |- (intp V env x).
  Proof.    
    destruct pr. apply (A m t). simpl; apply ps_k. simpl; apply ps_s. simpl; apply ps_a.
    apply (prop_soundness V env) in pr1. apply (ps_mp (intp V env x)).
    simpl in pr1; apply pr1.  apply (prop_soundness V env) in pr2. apply pr2.
    assumption. assumption.
  Defined.   

  Definition nil_prop_soundness
             (V: Type) (env: V -> P)
             (x: propositional_formula V) (pr: pf_hilbert_system_proof V nil x):
  |- (intp V env x).
  Proof.
    apply (prop_soundness V env nil). intros u F. inversion F. assumption.
  Defined.

  Definition lindenbaum_equivalence (x y:P):= prod (|- x -o y) (|- y -o x).

  Definition prop_to_lindenbaum_eq
             (V: Type) (env: V -> P) (a b: propositional_formula V):
    prod (pf_hilbert_system_proof V nil (pf_implies V a b))
         (pf_hilbert_system_proof V nil (pf_implies V b a)) -> 
    lindenbaum_equivalence (intp V env a) (intp V env b).
  Proof.
    intro M; destruct M as (M1, M2); apply (nil_prop_soundness V env) in M1; simpl in M1;
      apply (nil_prop_soundness V env) in M2; simpl in M2; simpl; split; assumption.
  Defined.

  Notation "$ q":= (pf_var nat q) (at level 41).
  
  Let env1 (a: P) (_: nat):P:= a.
  
  Let env2 (a b: P) (k:nat):P:=
    match k with
    |0 => a
    |1 => b
    |_ => a
    end.

  Let env3 (a b c:P) (k: nat):=
    match k with
    |0 => a
    |1 => b
    |2 => c
    |_ => a
    end.

  Let env4 (a b c d:P) (k: nat):=
    match k with
    |0 => a
    |1 => b
    |2 => c
    |3 => d
    |_ => a
    end.

  Ltac embed envi v w:= apply (prop_to_lindenbaum_eq nat envi ($ v) ($ w)).

  Definition generic_syllogism (x y z:P): |- x -o y -> |- y -o z -> |- x -o z. 
  Proof.
    intros A B. apply (ps_mp (x -o y)). apply (ps_mp (x -o y -o z)). apply ps_s.
    apply (ps_mp (y -o z)). apply ps_k. apply B. apply A.
  Defined.    
    
  Definition Lindenbaum_algebra: boolean_algebra.
  Proof.
    apply (make_ba P p_impl p_f lindenbaum_equivalence).
    intro x; embed (env1 x) 0 0; split; apply pfhs_i.
    intros x y z. intros A B. split. apply (generic_syllogism y x z). apply A. apply B.
    apply (generic_syllogism z x y). apply B. apply A. intros x x' y y' A B.
    assert
      (pf_hilbert_system_proof
         nat nil
         (pf_implies
            nat (pf_implies nat ($ 1) ($ 0))
            (pf_implies
               nat (pf_implies nat ($ 2) ($ 3))
               (pf_implies nat (pf_implies nat ($ 0) ($ 2)) (pf_implies nat ($ 1) ($ 3))))))
      as L. apply pfhs_polarity_formula.
    split. apply (ps_mp (y -o y')). apply (ps_mp (x' -o x)).
    apply (nil_prop_soundness nat (env4 x x' y y')) in L. simpl in L. assumption.
    apply A. apply B.
    apply (ps_mp (y' -o y)). apply (ps_mp (x -o x')).
    apply (nil_prop_soundness nat (env4 x' x y' y)) in L. simpl in L. assumption.
    apply A. apply B. intros.
    assert
      (pf_hilbert_system_proof
         nat nil
         (pf_implies
            nat
            (pf_implies
               nat (pf_false nat) ($ 2))
            (pf_implies nat ($ 1) (pf_implies nat ($ 0) ($ 1)))) *
       pf_hilbert_system_proof
         nat nil
         (pf_implies nat (pf_implies nat ($ 1) (pf_implies nat ($ 0) ($ 1)))
                     (pf_implies nat (pf_false nat) ($ 2)))) as L.
    apply pfhs_eq_k_explosion. apply (prop_to_lindenbaum_eq nat (env3 y x z)) in L; simpl in L.
    assumption.
    assert
      (pf_hilbert_system_proof
         nat nil
         (pf_implies
            nat (pf_implies nat ($ 0) (pf_implies nat ($ 1) ($ 2)))
            (pf_implies nat (pf_implies nat ($ 0) ($ 1)) (pf_implies nat ($ 0) ($ 2)))) *
       pf_hilbert_system_proof
         nat nil
         (pf_implies nat
                     (pf_implies nat (pf_implies nat ($ 0) ($ 1)) (pf_implies nat ($ 0) ($ 2)))
                     (pf_implies nat ($ 0) (pf_implies nat ($ 1) ($ 2))))
      )
      as L. apply pfhs_eq_s.
    intros; apply (prop_to_lindenbaum_eq nat (env3 x y z)) in L; simpl in L; assumption.
    assert
      (pf_hilbert_system_proof
         nat nil
         (pf_implies nat (pf_implies nat (pf_implies nat ($ 0) ($ 1)) ($ 0)) ($ 0)) *
       pf_hilbert_system_proof
         nat nil
         (pf_implies nat ($ 0) (pf_implies nat (pf_implies nat ($ 0) ($ 1)) ($ 0))))
      as L. apply pfhs_eq_peirce.
    intros; apply (prop_to_lindenbaum_eq nat (env2 x y)) in L; simpl in L; assumption.   
    assert (
        pf_hilbert_system_proof
          nat nil
          (pf_implies
             nat (pf_implies nat (pf_implies nat ($ 0) ($ 1)) ($ 1))
             (pf_implies nat (pf_implies nat ($ 1) ($ 0)) ($ 0))) *
        pf_hilbert_system_proof
          nat nil
          (pf_implies
             nat (pf_implies nat (pf_implies nat ($ 1) ($ 0)) ($ 0))
             (pf_implies nat (pf_implies nat ($ 0) ($ 1)) ($ 1)))
      ) as L. apply pfhs_eq_implies_or_permutation.
    intros; apply (prop_to_lindenbaum_eq nat (env2 x y)) in L; simpl in L; assumption.
  Defined.    
    
End Lindenbaum_algebras.

Section preorders.
  
  Polymorphic Cumulative Record preordered_class:Type:=
    make_po
      {
        po_domain: Type;
        po_relationship: po_domain -> po_domain -> Type;
        po_reflexivity: forall x:po_domain, po_relationship x x;
        po_transitivity: forall x y z:po_domain,
            po_relationship x y -> po_relationship y z -> po_relationship x z
      }.
  
End preorders.

Section Algebraic_identities_in_a_boolean_algebra.
  
  Variable B: boolean_algebra.                  

  Notation D:= (ba_domain B).
  Notation "x -o y":= (ba_implies B x y) (right associativity, at level 43).
  Notation "£":= (ba_false B) (at level 41).
  Notation T:= (ba_implies B (ba_false B) (ba_false B)).
  Notation "a == b" := (ba_equivalence B a b) (at level 44).

  Ltac refl:= apply ba_reflexivity.
  Ltac symtrans t:= apply ba_symmetry_and_transitivity with (x:= t).
  Ltac ap:= assumption.
  
  Definition ba_symmetry: forall x y: D, x == y -> y == x.
  Proof.
    intros x y A; symtrans x. apply A. refl.
  Defined.

  Ltac sym := apply ba_symmetry.

  Definition ba_transitivity: forall x y z:D, x == y -> y == z -> x == z.
  Proof.
    intros x y z P Q; symtrans y. sym; ap. ap.
  Defined.

  Ltac trans s := apply ba_transitivity with (y:= s). 

  Ltac cp:= apply ba_compatibility.
  
  Definition ba_left_computation: forall x y z:D, x == y -> (x -o z) == (y -o z).
  Proof.
    intros x y z E. cp. ap. refl.
  Defined.

  Ltac lcp:= apply ba_left_computation.

  Definition ba_right_computation: forall x y z:D, y == z -> (x -o y) == (x -o z).
  Proof.
    intros x y z E. cp. refl. ap.
  Defined.

  Ltac rcp:= apply ba_right_computation.

  Definition ba_explosion (x: D): T == £ -o x.
  Proof.
    trans (£ -o T). apply ba_axiom_1. sym; apply ba_axiom_1.
  Defined.
  
  Definition ba_implication_by_truth: forall x:D, T -o x == x.
  Proof.
    intro x. trans ((x -o (x -o x) -o x) -o x). lcp. apply ba_axiom_1. apply ba_peirce.
  Defined.     

  Ltac bor:= apply ba_implicative_or.

  Definition ba_truth_implied (x:D): T == x -o T.
  Proof.
    trans (T -o x -o T). apply ba_axiom_1. apply ba_implication_by_truth.
  Defined.
  
  Definition ba_implication_identity: forall x: D,
      T == x -o x.
  Proof.
    intros. trans ((x -o T) -o T). apply ba_truth_implied.
    trans ((T -o x) -o x). bor. lcp.  apply ba_implication_by_truth.
  Defined.

  Definition ba_truth_modus_ponens: forall x y: D,
      T == x -o y -> T == x -> T == y.
  Proof.
    intros x y P Q. trans (T -o y). trans (x -o y). ap. lcp. sym; ap.
    apply ba_implication_by_truth.
  Defined.      

  Ltac mp r:= apply ba_truth_modus_ponens with (x:= r).
  
  Definition ba_peirce_formula_is_true: forall x y:D, T == ((x -o y) -o x) -o x.
  Proof.
    intros x y. trans (x -o x). apply ba_implication_identity. lcp; sym; apply ba_peirce.
  Defined.

  Definition ba_equivalence_to_implication (x y:D): x == y -> T == x -o y.
  Proof.
    intros P. trans (x -o x). apply ba_implication_identity. rcp; apply P.
  Defined.

  Definition ba_s_formula (x y z:D): T == (x -o y -o z) -o (x -o y) -o x -o z.
  Proof.
    apply ba_equivalence_to_implication. apply ba_axiom_2.
  Defined.

  Definition ba_implies_increasing (x y z:D): T == y -o z -> T == (x -o y) -o (x -o z).
  Proof.
    intro A. trans (x -o y -o z). apply ba_truth_modus_ponens with (x:= y -o z).
    apply ba_axiom_1. apply A. apply ba_axiom_2.
  Defined.
  
  Definition ba_double_implication_to_equivalence (x y:D):
    T == x -o y -> T == y -o x -> x == y.
  Proof.
    intros P Q. trans ((x -o y) -o y). trans ((y -o x) -o x). trans (T -o x).
    sym; apply ba_implication_by_truth. lcp; apply Q. bor. symtrans (T -o y). lcp; ap.
    apply ba_implication_by_truth.
  Defined.
  
  Definition ba_double_negation (x:D): (x -o £) -o £ == x.
  Proof.
    trans (T -o x). trans ((£ -o x) -o x). bor. lcp. sym; apply ba_explosion.
    apply ba_implication_by_truth.
  Defined.

  Definition ba_double_negation_formula (x: D): T == ((x -o £) -o £) -o x.
  Proof.
    trans (x -o x). apply ba_implication_identity. sym; lcp; apply ba_double_negation.
  Defined.

  Section interpretation_of_propositional_proofs_in_a_boolean_algebra.

    Variable V: Type.
    Variable env: V -> D.

    Notation P:= (propositional_formula V).

    Variable l: list P.
    
    Notation memb:= (type_valued_list_member (propositional_formula V)).
    Notation intp:= (prop_interpreter V D (ba_implies B) (ba_false B) env).      
    Notation prov:= (pf_hilbert_system_proof V l).      

    Variable hyp_list_true: forall u:P, (memb u l) -> T == intp u.
    
    Definition ba_prop_soundness: forall x:P, prov x -> T == intp x.
    Proof.
      apply prop_soundness. intros; apply ba_axiom_1. apply ba_s_formula.
      apply ba_double_negation_formula. apply ba_truth_modus_ponens. apply hyp_list_true.
    Defined.

    Definition ba_prop_equalities (x y:P):
      prod (prov (pf_implies V x y)) (prov (pf_implies V y x)) -> intp x == intp y.
    Proof.
      intro M; destruct M as (M1, M2); apply ba_prop_soundness in M1;
        apply ba_prop_soundness in M2; simpl in M1; simpl in M2.
      apply ba_double_implication_to_equivalence; assumption.
    Defined.         
    
  End interpretation_of_propositional_proofs_in_a_boolean_algebra.

  Notation intp:=
    (fun env: nat -> D => prop_interpreter nat D (ba_implies B) (ba_false B) env).
  Notation "|- p":= (pf_hilbert_system_proof nat nil p) (at level 34).
  Notation "m § n":= (pf_implies nat m n) (right associativity, at level 33).
  Notation µ:= (pf_false nat).
  Notation "$ k":= (pf_var nat k) (at level 32).
  Notation p_and := (pf_and nat).
  Notation p_or := (pf_or nat).
  Notation P:= (propositional_formula nat).
  
  Definition ba_proof_exploitation (env: nat -> D) (x: P): |- x -> T == intp env x.
  Proof.
    apply ba_prop_soundness. intros u F; inversion F.
  Defined.

  Notation provably_equal:= (fun a b: P => prod (|- a § b) (|- b § a)).

  Definition ba_provable_equality_exploitation (env: nat -> D) (x y:P):
    provably_equal x y -> intp env x == intp env y.
  Proof.
    apply ba_prop_equalities. intros u F; inversion F.
  Defined.

  Ltac exploit envi p q:= apply (ba_provable_equality_exploitation envi p q). 
  
  Notation env1 := (fun (a: D) (_: nat) => a: D).

  Notation env2:= (fun (a b: D) (k:nat) =>
                     match k with
                     |0 => a
                     |1 => b
                     |_ => a
                     end: D).

  Notation env3:= (fun (a b c:D) (k: nat) =>
                     match k with
                     |0 => a
                     |1 => b
                     |2 => c
                     |_ => a
                     end: D).

  Notation env4:= (fun (a b c d:D) (k: nat) =>
                     match k with
                     |0 => a
                     |1 => b
                     |2 => c
                     |3 => d
                     |_ => a
                     end: D).
  
  Definition ba_not (x:D): D:= x -o £.
  
  Definition ba_or (x y:D):D:= (x -o £) -o y.

  Definition ba_and (x y:D):= (x -o y -o £) -o £.

  Definition ba_or_equivalence (x y:D): ba_or x y == (x -o y) -o y.
  Proof.
    exploit (env2 x y) (p_or ($0) ($1)) (($0 § $1) § $1). apply pfhs_eq_or_equivalence.
  Defined.

  Definition ba_and_or_compatibility (x x' y y': D):
    x == x' -> y == y' -> prod (ba_and x y == ba_and x' y') (ba_or x y == ba_or x' y').
  Proof.
    intros ex ey. split. lcp. apply ba_compatibility. ap. lcp; ap.
    apply ba_compatibility. lcp; ap. ap.
  Defined.

  Definition ba_not_compatibility (x x':D): x == x' -> ba_not x == ba_not x'.
  Proof.
    intros; lcp; ap.
  Defined.

  Definition ba_heyting_identity (x y z:D): (ba_and x y) -o z == x -o y -o z.
  Proof.
    exploit (env3 x y z) ((p_and ($0) ($1)) § $2) ($0 § $1 § $2). apply pfhs_eq_heyting.
  Defined.

  Section The_Boole_algebra_as_a_Heyting_algebra.

    Definition ba_order (x y: D):= T == x -o y.

    Definition bao_reflexivity: forall x: D, ba_order x x.
    Proof.
      intro x; apply ba_implication_identity.
    Defined.

    Definition bao_reflexivity_2:
      forall x y:D, x == y -> ba_order x y.
    Proof.
      intros x y; apply ba_equivalence_to_implication.
    Defined.
    
    Definition bao_anti_symmetry: forall x y:D, ba_order x y -> ba_order y x -> x == y.
    Proof.
      intros x y; apply ba_double_implication_to_equivalence.
    Defined.

    Definition bao_transitivity:
      forall x y z:D, ba_order x y -> ba_order y z -> ba_order x z.
    Proof.
      intros x y z P Q. apply (ba_truth_modus_ponens (x -o y)).
      apply (ba_truth_modus_ponens (y -o z)).
      apply (ba_proof_exploitation (env3 x y z) (($1 § $2) § ($0 § $1) § ($0 § $2))).
      apply pfhs_b. apply Q. apply P.
    Defined.

    Definition bao_false_is_min: forall x:D, ba_order (£) x.
    Proof.
      apply ba_explosion.
    Defined.

    Definition bao_true_is_max: forall x:D, ba_order x T.
    Proof.
      intros; apply ba_truth_implied.
    Defined.
    
    Definition bao_and_is_an_inf: forall x y z:D,
        prod (prod (ba_order z x) (ba_order z y) -> ba_order z (ba_and x y))
             (ba_order z (ba_and x y) -> prod (ba_order z x) (ba_order z y)).
    Proof.
      intros; split. intro M. 
      apply (ba_truth_modus_ponens (z -o y)).
      apply (ba_truth_modus_ponens (z -o y -o (ba_and x y))). apply ba_s_formula.
      apply bao_transitivity with (y:= x). apply M.
      apply (ba_proof_exploitation (env2 x y) ($0 § $1 § (p_and ($0) ($1)))).
      apply pfhs_and_intro. apply M. intro N; split.
      apply bao_transitivity with (y:= ba_and x y). apply N. 
      apply (ba_proof_exploitation (env2 x y) ((p_and ($0) ($1)) § $0)).
      apply pfhs_and_left_elim. apply bao_transitivity with (y:= ba_and x y). apply N. 
      apply (ba_proof_exploitation (env2 x y) ((p_and ($0) ($1)) § $1)).
      apply pfhs_and_right_elim. 
    Defined.               

    Definition bao_or_is_a_sup: forall (x y z:D),
        prod (prod (ba_order x z) (ba_order y z) -> ba_order (ba_or x y) z)
             (ba_order (ba_or x y) z -> prod (ba_order x z) (ba_order y z)).
    Proof.
      intros x y z. split. intro M. apply (ba_truth_modus_ponens (y -o z)).        
      apply (ba_truth_modus_ponens (x -o z)).
      apply (ba_proof_exploitation
               (env3 x y z)
               (($0 § $2) §($1 § $2) §(p_or ($0) ($1)) § $2)). apply pfhs_or_elim.
      apply M. apply M. intro N; split. apply bao_transitivity with (y:= ba_or x y).
      apply (ba_proof_exploitation (env2 x y) ($0 § p_or ($0) ($1))).
      apply pfhs_or_left_intro. assumption.  apply bao_transitivity with (y:= ba_or x y).
      apply (ba_proof_exploitation (env2 x y) ($1 § p_or ($0) ($1))).
      apply pfhs_or_right_intro. assumption. 
    Defined.        
    
    Definition bao_adjunction_between_conjunction_and_implies: forall (x y z:D),
        prod (ba_order (ba_and x y) z -> ba_order x (y -o z))
             (ba_order x (y -o z) -> ba_order (ba_and x y) z).
    Proof.
      intros x y z; split. intros M. trans ((ba_and x y) -o z). apply M.
      apply ba_heyting_identity.
      intros M; trans (x -o y -o z). apply M. sym; apply ba_heyting_identity.
    Defined.

    Definition bao_reductio_ad_absurdum (x: D): ba_order ((x -o £) -o £) x.
    Proof.
      apply ba_double_negation_formula.
    Defined.

    Definition bao_and_elim (x y:D): prod (ba_order (ba_and x y) x) (ba_order (ba_and x y) y).
    Proof.
      split. apply bao_and_is_an_inf with (y:= y); apply bao_reflexivity.
      apply bao_and_is_an_inf with (x:= x); apply bao_reflexivity.
    Defined.
    
    Definition ba_and_commutative (x y:D): ba_and x y == ba_and y x.
    Proof.
      assert (forall a b:D, ba_order (ba_and a b) (ba_and b a)) as F. intros.      
      apply bao_and_is_an_inf; split; apply bao_and_elim.  
      apply bao_anti_symmetry; apply F.
    Defined.

    Definition ba_and_associative (x y z:D): ba_and (ba_and x y) z == ba_and x (ba_and y z).
    Proof.
      apply bao_anti_symmetry. apply bao_and_is_an_inf; split.
      apply bao_transitivity with (y:= ba_and x y); apply bao_and_elim.
      apply bao_and_is_an_inf. split.
      apply bao_transitivity with (y:= ba_and x y); apply bao_and_elim.
      apply bao_and_elim. apply bao_and_is_an_inf; split. apply bao_and_is_an_inf; split.
      apply bao_and_elim. apply bao_transitivity with (y:= ba_and y z); apply bao_and_elim.
      apply bao_transitivity with (y:= ba_and y z); apply bao_and_elim.
    Defined.

    Definition ba_and_idempotent (x:D): ba_and x x == x.
    Proof.
      apply bao_anti_symmetry. apply bao_and_elim.
      apply bao_and_is_an_inf; split; apply bao_reflexivity.
    Defined.

    Definition bao_or_intro (x y:D): prod (ba_order x (ba_or x y)) (ba_order y (ba_or x y)).
    Proof.
      split. apply bao_or_is_a_sup with (y:= y); apply bao_reflexivity.
      apply bao_or_is_a_sup with (x:= x); apply bao_reflexivity.
    Defined.
    
    Definition ba_or_commutative (x y:D): ba_or x y == ba_or y x.
    Proof.
      assert (forall a b:D, ba_order (ba_or a b) (ba_or b a)) as F. intros.
      apply bao_or_is_a_sup; split; apply bao_or_intro.  
      apply bao_anti_symmetry; apply F.
    Defined.

    Definition ba_or_associative (x y z:D): ba_or (ba_or x y) z == ba_or x (ba_or y z).
    Proof.
      apply bao_anti_symmetry. apply bao_or_is_a_sup; split.
      apply bao_or_is_a_sup; split.
      apply bao_or_intro. apply bao_transitivity with (y:= ba_or y z); apply bao_or_intro.
      apply bao_transitivity with (y:= ba_or y z); apply bao_or_intro.
      apply bao_or_is_a_sup; split.
      apply bao_transitivity with (y:= ba_or x y); apply bao_or_intro.
      apply bao_or_is_a_sup; split.   
      apply bao_transitivity with (y:= ba_or x y); apply bao_or_intro. apply bao_or_intro. 
    Defined.

    Definition ba_or_idempotent (x:D): ba_or x x == x.
    Proof.
      apply bao_anti_symmetry. 
      apply bao_or_is_a_sup; split; apply bao_reflexivity. apply bao_or_intro.
    Defined.

    (** The following theorem is not true in an arbitrary lattice, see for instance 
     the set of subvector spaces of a given vector space. The use of Heyting algebra 
     properties are needed. *)
    
    Definition ba_and_or_distributivity (x y z:D):
      ba_and (ba_or x y) z == ba_or (ba_and x z) (ba_and y z).
    Proof.
      apply bao_anti_symmetry. apply bao_adjunction_between_conjunction_and_implies.
      apply bao_or_is_a_sup; split; apply bao_adjunction_between_conjunction_and_implies;
        apply bao_or_intro. apply bao_or_is_a_sup; split; apply bao_and_is_an_inf; split.
      apply bao_transitivity with (y:= x). apply bao_and_elim. apply bao_or_intro.
      apply bao_and_elim. apply bao_transitivity with (y:= y). apply bao_and_elim.
      apply bao_or_intro. apply bao_and_elim. 
    Defined.
      
    (** The same remark applies here*)
        Definition ba_or_and_distributivity (x y z:D):
      ba_or (ba_and x y) z == ba_and (ba_or x z) (ba_or y z).
    Proof.
      apply bao_anti_symmetry. apply bao_or_is_a_sup; split; apply bao_and_is_an_inf; split.
      apply bao_transitivity with (y:= x). apply bao_and_elim. apply bao_or_intro.
      apply bao_transitivity with (y:= y). apply bao_and_elim. apply bao_or_intro.
      apply bao_or_intro. apply bao_or_intro.
      apply bao_adjunction_between_conjunction_and_implies. apply bao_or_is_a_sup. split.
      apply bao_adjunction_between_conjunction_and_implies.
      apply bao_transitivity with (y:=ba_or (ba_and y x) (ba_and z x)).
      apply bao_transitivity with (y:=ba_and (ba_or y z) x).
      apply bao_reflexivity_2; apply ba_and_commutative.
      apply bao_reflexivity_2; apply ba_and_or_distributivity. apply bao_or_is_a_sup; split.
      apply bao_transitivity with (y:=ba_and x y).
      apply bao_reflexivity_2; apply ba_and_commutative. apply bao_or_intro.
      apply bao_transitivity with (y:= z). apply bao_and_elim. apply bao_or_intro.      
      apply bao_adjunction_between_conjunction_and_implies.
      apply bao_transitivity with (y:=ba_or (ba_and y z) (ba_and z z)).
      apply bao_transitivity with (y:=ba_and (ba_or y z) z).
      apply bao_reflexivity_2; apply ba_and_commutative.
      apply bao_reflexivity_2; apply ba_and_or_distributivity.
      apply bao_or_is_a_sup; split; apply bao_transitivity with (y:= z).
      apply bao_and_elim. apply bao_or_intro. apply bao_and_elim. apply bao_or_intro.
    Defined.      
    
    Definition bao_permutation_not (x y:D): ba_order x (ba_not y) -> ba_order y (ba_not x).
    Proof.
      unfold ba_order; intros F. trans ((ba_and x y) -o £). trans (x -o y -o £).
      apply F. sym; apply ba_heyting_identity.
      trans ((ba_and y x) -o £). lcp. apply ba_and_commutative. apply ba_heyting_identity.
    Defined.        

    Definition bao_decreasing_not (x y:D): ba_order x y -> ba_order (ba_not y) (ba_not x).
    Proof.
      intros P. apply bao_permutation_not. apply bao_transitivity with (y:= y). apply P.
      apply bao_reflexivity_2; sym; apply ba_double_negation.
    Defined.

  End The_Boole_algebra_as_a_Heyting_algebra.

  Definition ba_non_contradiction (x: D): £ == ba_and x (ba_not x). 
  Proof.
    trans (ba_and (ba_not x) x). trans (T -o £). sym; apply ba_implication_by_truth.
    lcp; apply ba_implication_identity. apply ba_and_commutative.
  Defined.
    
  Definition ba_de_morgan_laws (x y:D):
    prod (ba_not (ba_and x y) == ba_or (ba_not x) (ba_not y))
         (ba_not (ba_or x y) == ba_and (ba_not x) (ba_not y)).
  Proof.
    assert
      (forall x1 y1:D, (ba_not (ba_or x1 y1) == ba_and (ba_not x1) (ba_not y1))) as L.
    intros x1 y1; apply bao_anti_symmetry.
    apply bao_and_is_an_inf; split; apply bao_decreasing_not; apply bao_or_intro.
    apply bao_decreasing_not. apply bao_or_is_a_sup; split.
    apply bao_adjunction_between_conjunction_and_implies. apply bao_transitivity with (y:= £).
    apply bao_reflexivity_2; sym; apply ba_non_contradiction. apply ba_explosion.
    apply bao_transitivity with (y:= ba_not y1 -o £). apply bao_permutation_not.
    apply bao_reflexivity. apply ba_axiom_1. split. sym.
    trans (ba_not (ba_not (ba_or (ba_not x) (ba_not y)))). sym; apply ba_double_negation.
    apply ba_not_compatibility. trans (ba_and (ba_not (ba_not x)) (ba_not (ba_not y))).
    apply L. apply ba_and_or_compatibility; apply ba_double_negation. apply L.
  Defined.

  Definition ba_excluded_middle (x: D): T == ba_or x (ba_not x).
  Proof.
    apply ba_implication_identity.
  Defined.

  Definition ba_implies_with_disjunction_and_negation (x y:D): x -o y == ba_or (ba_not x) y.
  Proof.
    lcp; sym; apply ba_double_negation.
  Defined.    

  (** The following result will be used later when we'll show how to embed any boolean
   algebra into a complete boolean algebra.*)
  
  Definition ba_order_is_separative:
    forall x y : D,
      (forall s : D,
          ba_order s x ->
          (forall r : D, ba_order r s -> ba_order r y -> £ == r) -> £ == s) ->
      ba_order x y.
  Proof.
    intros x y A. assert (£ == ba_and x (y -o £)) as L. trans (ba_and (y -o £) x). apply A.
    destruct (bao_and_is_an_inf (y -o £) x (ba_and (y -o £) x)) as (P,Q).
    apply Q; apply bao_reflexivity. intros r M N. apply bao_anti_symmetry.
    apply bao_false_is_min. apply ba_truth_modus_ponens with (x := r -o y).
    apply ba_truth_modus_ponens with (x:= r -o (y -o £)). apply ba_s_formula.
    apply (bao_and_is_an_inf (y -o £) x); apply M. apply N. apply ba_and_commutative.
    apply ba_left_computation with (z:= £) in L. trans ((ba_and x (y -o £)) -o £).
    apply L. trans (x -o (y -o £) -o £). apply ba_heyting_identity. rcp.
    apply ba_double_negation.
  Defined.
  
End Algebraic_identities_in_a_boolean_algebra.  

Section Complete_boolean_algebra_associated_to_a_preorder.

  Variable PC: preordered_class.

  Notation E:= (po_domain PC). 

  Variable W: E -> Type.

  Notation po:= (po_relationship PC).  
  Notation po_refl:= (po_reflexivity PC).  
  Notation po_trans:= (po_transitivity PC).

  Variable W_stable: forall x y:E, W y -> po x y -> W x.

 
  Ltac refl:= apply po_refl.
  Ltac trans v:= apply po_trans with (y:= v).

  Definition po_implies (M N: E -> Type) (t: E):Type:= forall s:E, po s t -> (M s) -> (N s).

  Definition po_stable (F: E -> Type):= forall x y:E, F y -> po x y -> F x.

  Definition po_implies_stable (F G: E -> Type): po_stable (po_implies F G).
  Proof.
    unfold po_stable. unfold po_implies. intros x y P Q s R. apply P. trans x; assumption.
  Defined.

  Definition po_dual (F: E -> Type):= po_implies F W.

  Notation incl:= (fun F G: E -> Type => forall x:E, F x -> G x).
  
  Definition po_double_dual_introduction: forall (A: E -> Type), po_stable A ->
                                                                 incl A (po_dual (po_dual A)).
  Proof.
    intros A P0 x P1 y P2 P3. apply P3. refl. apply P0 with (y:= x); assumption.
  Defined.

  Notation "A == B":= (prod (incl A B) (incl B A)) (at level 44).

  Definition po_regular_implies_stable (A: E -> Type): A == po_dual (po_dual A) -> po_stable A.
  Proof.
    unfold po_dual; intros M x y N P. destruct M as (M1, M2). apply M1 in N.
    apply M2. apply (po_implies_stable (po_implies A W) W x) in N; assumption.
  Defined.

  Definition regular_segment:Type:= {f: E -> Type & f == po_dual (po_dual f)}.

  Definition rs_false: regular_segment.
  Proof.
    exists W. split. apply po_double_dual_introduction. unfold po_stable; apply W_stable.
    unfold po_dual. unfold po_implies. intros x P. apply P. refl. intros; assumption.
  Defined.

  Definition rs_implies (A B: regular_segment): regular_segment.
  Proof.
    exists (po_implies (projT1 A) (projT1 B)). split.
    intros x C y Q R. apply R. refl. apply (po_implies_stable (projT1 A) (projT1 B) y) in C.
    apply C. apply Q. intros x P1 y R1 P2. apply (projT2 B). intros z P3 P4. apply P1.
    trans y; assumption. intros t P5 P6. apply P4. apply P5. apply P6. refl.
    apply (po_regular_implies_stable (projT1 A) (projT2 A) t y). apply P2.
    trans z; assumption.
  Defined.    

  Definition rs_all (T: Type) (f: T -> regular_segment): regular_segment.
  Proof.
    exists (fun x: E => forall i: T, projT1 (f i) x). split. intros x P y Q R. apply R. refl.
    intro i. apply (po_regular_implies_stable (projT1 (f i)) (projT2 (f i)) y x). apply P.
    apply Q. intros x P j. apply (projT2 (f j)). intros y Q R. apply P. apply Q.
    intros z M N. apply R. apply M. apply N.
  Defined.    

  Definition rs_extensional_equality (F G: regular_segment):= (projT1 F) == (projT1 G).

  Definition cba_regular_segments: complete_boolean_algebra.
  Proof.
    apply (make_cba regular_segment rs_implies rs_false rs_all rs_extensional_equality).
    intros; split; intros; assumption. intros x y z M N; split.
    intros t Q; apply N; apply M; apply Q. intros t Q; apply M; apply N; apply Q.
    intros x x' y y' P Q; split.
    intros t R1 s R2 R3; apply Q; apply R1. apply R2. apply P; apply R3.
    intros t R1 s R2 R3; apply Q; apply R1. apply R2. apply P; apply R3.
    intros x y z; split. intros s P t1 Q1 Q2 t2 Q3 Q4.    
    apply (po_regular_implies_stable (projT1 x) (projT2 x) t2 t1); assumption.
    intros t P s Q R. apply (projT2 z). intros r M N. apply (W_stable r s). apply R. apply M.
    intros x y z; split. intros s P t1 Q1 R1 t2 Q2 R2.
    assert (projT1 (rs_implies y z) t2) as L. apply P. trans t1. apply Q2. apply Q1. apply R2.
    apply L. refl. apply R1. apply Q2. apply R2. intros s P t1 Q1 R1 t2 Q2 R2.
    assert (projT1 (rs_implies x y) t2) as L1. intros s1 Q3 Q4.
    apply (po_regular_implies_stable (projT1 y) (projT2 y) s1 t2); assumption.
    apply P in L1. apply L1. refl. 
    apply (po_regular_implies_stable (projT1 x) (projT2 x) t2 t1); assumption.
    trans t1; assumption. intros x y; split. intros s P. apply (projT2 x).
    intros t1 P1 Q1. apply Q1. refl. apply P. apply P1. intros t2 P2 Q2. apply (projT2 y).
    intros t3 P3 Q3. apply (W_stable t3 t2). 
    apply (po_implies_stable (projT1 x) W t2 t1). apply Q1. apply P2. refl. apply Q2. apply P3.
    intros s P t Q R. apply (po_regular_implies_stable (projT1 x) (projT2 x) t s); assumption.
    intros x y; split.    
    intros s P1 t1 Q1 R1. apply (projT2 x). intros t2 P2 Q2. apply Q2. refl. apply R1.
    apply P2. apply P1. trans t1; assumption. intros t3 P3 Q3. apply Q2 in P3. apply P3 in Q3.
    apply (projT2 y). intros t4 P4 Q4. apply (W_stable t4 t3). apply Q3. apply P4.
    intros s P1 t1 Q1 R1. apply (projT2 y). intros t2 P2 Q2. apply Q2. refl. apply R1.
    apply P2. apply P1. trans t1; assumption. intros t3 P3 Q3. apply Q2 in P3. apply P3 in Q3.
    apply (projT2 x). intros t4 P4 Q4. apply (W_stable t4 t3). apply Q3. apply P4.
    intros x T f; split; unfold rs_extensional_equality; simpl; unfold po_implies; intro K.
    destruct K as (K1, K2). split. intros y M z N P. apply K1 with (x0:= y) (s:= z).
    apply M. apply N. apply P. intros y P z Q R; apply R. split. intros y P z Q R j.
    destruct (K j) as (K1, K2). apply (K1 y). apply P. apply Q. apply R.     
    intros; assumption.
  Defined.

  Definition rs_canonical_morphism (u: E): regular_segment.
  Proof.
    exists (po_dual (po_dual (fun s: E => po s u))). split.
    apply po_double_dual_introduction;
      apply (po_implies_stable (po_dual (fun v: E => po v u)) W).
    intros s P t Q R. apply P. apply Q. apply po_double_dual_introduction.
    apply (po_implies_stable (fun v: E => po v u) W). apply R.
  Defined.

  Definition po_dual_decreasing (x y: E -> Type): incl x y -> incl (po_dual y) (po_dual x).
  Proof.
    intros P t Q s R1 R2; apply Q. apply R1. apply P; apply R2.
  Defined.

  Let ord:=
      (fun x y: regular_segment => 
         cba_equivalence cba_regular_segments
                         (cba_implies cba_regular_segments
                                      (cba_false cba_regular_segments)
                                      (cba_false cba_regular_segments))
                         (cba_implies cba_regular_segments x y)). 

    Definition po_incl_ba_order (x y: regular_segment):
      prod (incl (projT1 x) (projT1 y) -> ord x y)
           (ord x y -> incl (projT1 x) (projT1 y)).
    Proof.
      simpl. split. intro P1. split. intros t P2 s P3. apply P1.
      intros; simpl; intros s M N; assumption. intros P t Q. destruct P as (P1, P2).
      simpl in P1. apply (P1 t). intros s M N; assumption. refl. apply Q.
    Defined.           
  
  Definition rs_po_canonical_morphism_increasing (x y:E):
    po x y -> incl (projT1 (rs_canonical_morphism x)) (projT1 (rs_canonical_morphism y)).
  Proof.
    simpl; intros P. repeat apply po_dual_decreasing. intros; trans x; assumption.
  Defined.

  Definition rs_ba_canonical_morphism_increasing (x y:E):
    po x y -> ord (rs_canonical_morphism x) (rs_canonical_morphism y).
  Proof.
    intro P; apply po_incl_ba_order; apply rs_po_canonical_morphism_increasing; apply P.
  Defined.

  Definition po_separative_strictly_increasing:
    (forall x t: E, po_dual (po_dual (fun s: E => po s x)) t -> po t x) ->
    forall x y:E,
      incl (projT1 (rs_canonical_morphism x)) (projT1 (rs_canonical_morphism y)) -> po x y.
  Proof.
    intros sep x y P. simpl in P. apply sep. apply P. apply po_double_dual_introduction.
    intros t u M N; trans u; assumption. refl.
  Defined.
  
  Definition rs_po_canonical_morphism_equality:
    forall x y:E, po x y -> po y x ->
                  rs_extensional_equality (rs_canonical_morphism x) (rs_canonical_morphism y).
  Proof.
    intros; split; apply rs_po_canonical_morphism_increasing; assumption.
  Defined.

  Definition rs_ba_canonical_morphism_equality:
    forall x y:E, po x y -> po y x ->
                  cba_equivalence
                    cba_regular_segments
                    (rs_canonical_morphism x) (rs_canonical_morphism y).
  Proof.
    intros. simpl. apply rs_po_canonical_morphism_equality; assumption.
  Defined.
  
  Definition po_separative_canonical_morphism_injectivity:
    (forall x t: E, po_dual (po_dual (fun s: E => po s x)) t -> po t x) ->
    forall x y:E,
      rs_extensional_equality (rs_canonical_morphism x) (rs_canonical_morphism y) ->
      prod (po x y) (po y x).
  Proof.
    intros sep x y P. split; apply po_separative_strictly_increasing. apply sep. apply P.
    apply sep. apply P.
  Defined.

  Definition ba_separative_canonical_morphism_injectivity:
    (forall x t: E, po_dual (po_dual (fun s: E => po s x)) t -> po t x) ->
    forall x y:E,
      cba_equivalence
         cba_regular_segments
         (rs_canonical_morphism x) (rs_canonical_morphism y) ->
      prod (po x y) (po y x).
  Proof.
    simpl; apply po_separative_canonical_morphism_injectivity. 
  Defined.   
  
End Complete_boolean_algebra_associated_to_a_preorder.

Section The_embedding_of_any_boolean_algebra_into_a_complete_boolean_algebra.
  
  Variable B: boolean_algebra.

  Notation D:= (ba_domain B).
  Notation "x -o y":= (ba_implies B x y) (right associativity, at level 43).
  Notation "£":= (ba_false B) (at level 41).
  Notation T:= (ba_implies B (ba_false B) (ba_false B)).
  Notation "a == b" := (ba_equivalence B a b) (at level 44). 

  Definition ba_as_preorder: preordered_class:=
    make_po D (ba_order B) (bao_reflexivity B) (bao_transitivity B).      
  
  Definition ba_completion: complete_boolean_algebra.
  Proof.
    apply (cba_regular_segments ba_as_preorder (fun a: D => ba_false B == a)).
    simpl. intros x y M N. apply bao_anti_symmetry. apply bao_false_is_min.
    apply bao_transitivity with (y:= y). apply N. apply bao_reflexivity_2.
    apply ba_symmetry; apply M.
  Defined.

  Notation B':= ba_completion. 
  Notation D':= (cba_domain ba_completion).                     
  
  Definition ba_to_cba_embedding (x: D): D':=
    rs_canonical_morphism ba_as_preorder (fun a: D => ba_false B == a) x.
  
  Definition btce_injective (x y:D):
    prod (x == y -> cba_equivalence B' (ba_to_cba_embedding x) (ba_to_cba_embedding y))
         (cba_equivalence B' (ba_to_cba_embedding x) (ba_to_cba_embedding y) -> x == y).
  Proof.
    split. intro P. apply rs_ba_canonical_morphism_equality.
    apply bao_reflexivity_2; apply P. apply bao_reflexivity_2; apply ba_symmetry; apply P.
    intro Q; apply ba_separative_canonical_morphism_injectivity in Q.
    apply bao_anti_symmetry; apply Q. intros a b. apply ba_order_is_separative.
  Defined.

  Definition btce_morphism: forall (x y:D),
      cba_equivalence B'
                      (ba_to_cba_embedding (x -o y))
                      (cba_implies B' (ba_to_cba_embedding x) (ba_to_cba_embedding y)).
  Proof.
    intros x y. simpl. split. simpl. unfold po_dual. unfold po_implies. simpl.
    intros t P s Q R r M N. apply R. apply M. intros u E F. apply P.
    apply bao_transitivity with (y:= r). apply E.  
    apply bao_transitivity with (y:= s). apply M. apply Q.
    intros v A1 A2. apply N. apply bao_transitivity with (y:= u). apply A1. apply E.
    apply bao_transitivity with (y:= ba_and B (x -o y) x). apply bao_and_is_an_inf. split. 
    apply A2. apply bao_transitivity with (y:= u). apply A1. apply F.
    apply ba_transitivity with (y:= (x -o y) -o (x -o y)).
    apply ba_implication_identity. apply ba_symmetry; apply ba_heyting_identity.
    intros t. simpl. unfold po_dual. unfold po_implies. simpl.
    intros P s Q R. apply (P s Q). intros u A1 A2. apply R. apply A1.
    assert (£ == ba_and B u (ba_and B x (y -o £))) as L1. apply A2.
    apply bao_and_is_an_inf with (x:= u) (y:= ba_and B x (y -o £)); apply bao_reflexivity.
    apply bao_transitivity with (y:= ba_and B x (y -o £)).
    apply bao_and_is_an_inf with (x:= u) (y:= ba_and B x (y -o £)); apply bao_reflexivity.
    apply bao_and_is_an_inf with (x:= x) (y:= (y -o £)); apply bao_reflexivity.
    apply ba_left_computation with (z:= £) in L1.
    assert (T == u -o (ba_and B x (y -o £)) -o £) as L2.
    apply ba_transitivity with (y:= ba_and B u (ba_and B x (y -o £)) -o £). apply L1.
    apply ba_heyting_identity.
    apply ba_transitivity with (y:= u -o (ba_and B x (y -o £) -o £)). apply L2.
    apply ba_right_computation. 
    apply ba_transitivity with (y:= x -o (y -o £) -o £). apply ba_heyting_identity.
    apply ba_right_computation. apply ba_double_negation. apply bao_reflexivity.
    intros r A1 A2. apply R. apply A1. apply bao_transitivity with (y:= y). apply A2.
    apply ba_axiom_1.
  Defined.
  
  Definition btce_false:
    cba_equivalence B' (ba_to_cba_embedding (ba_false B)) (cba_false B').
  Proof.
    split. simpl. intros x A. apply A. simpl. apply bao_reflexivity. intros t P Q.
    apply bao_anti_symmetry. apply ba_explosion. apply Q. intros x Q s R P.
    apply P. apply bao_reflexivity. simpl in Q. apply bao_transitivity with (y:= x).
    apply R. apply bao_reflexivity_2. apply ba_symmetry. apply Q.
  Defined.             
  
End The_embedding_of_any_boolean_algebra_into_a_complete_boolean_algebra.

Section cba_to_ba.

  (** It could seem baffling that we define this operation only here but it is 
   to avoid universes inconsistencies. *)
  
  Variable B: complete_boolean_algebra.

  Definition cba_to_ba: boolean_algebra:=
    make_ba (cba_domain B) (cba_implies B) (cba_false B) (cba_equivalence B)
            (cba_reflexivity B) (cba_symmetry_and_transitivity B)
            (cba_compatibility B) (cba_axiom_1 B) (cba_axiom_2 B) (cba_peirce B)
            (cba_implicative_or B).
  
End cba_to_ba.

Section the_complete_case.

  Variable C: complete_boolean_algebra.

  Definition cba_symmetry (x y: cba_domain C):
    cba_equivalence C x y -> cba_equivalence C y x.
  Proof.
    apply (ba_symmetry (cba_to_ba C)).
  Defined.
  
  Definition cba_order:= ba_order (cba_to_ba C).

  Definition cbao_reflexivity: forall x: cba_domain C, cba_order x x.
  Proof.
    unfold cba_order; intro. apply bao_reflexivity.
  Defined.

  Definition cbao_reflexivity_2:
    forall x y:cba_domain C, cba_equivalence C x y -> cba_order x y.
  Proof.
    unfold cba_order; intros x y E. apply bao_reflexivity_2. simpl. apply E.
  Defined.
  
  Definition cbao_anti_symmetry:
    forall x y:cba_domain C, cba_order x y -> cba_order y x -> cba_equivalence C x y.
  Proof.
    intros x y; unfold cba_order; unfold cba_equivalence; apply bao_anti_symmetry.
  Defined.

  Definition cbao_transitivity:
    forall x y z:cba_domain C,
      cba_order x y -> cba_order y z -> cba_order x z.
  Proof.
    intros x y z; unfold cba_order. apply bao_transitivity.
  Defined.

  Definition cba_forall_is_an_inf (T: Type) (f: T -> cba_domain C) (m: cba_domain C):
    prod (cba_order m (cba_all C T f) -> forall i:T, cba_order m (f i))
         ((forall i:T, cba_order m (f i)) -> cba_order m (cba_all C T f)).
  Proof.
    apply cba_all_inf. 
  Defined.    

  Definition cba_forall_special_case (T: Type) (f: T -> cba_domain C) (j: T):
    cba_order (cba_all C T f) (f j).
  Proof.
    apply cba_all_inf; apply (ba_implication_identity (cba_to_ba C)).
  Defined.
  
  Definition cba_forall_implies (T: Type) (f: T -> cba_domain C) (m: cba_domain C):
    cba_equivalence C
                    (cba_all C T (fun i: T => cba_implies C m (f i)))
                    (cba_implies C m (cba_all C T f)).
  Proof.
    apply (bao_anti_symmetry (cba_to_ba C)).
    apply (bao_adjunction_between_conjunction_and_implies
             (cba_to_ba C) (cba_all C T (fun i: T => cba_implies C m (f i)))
             m (cba_all C T f)).
    apply cba_forall_is_an_inf. intro j.
    apply (bao_adjunction_between_conjunction_and_implies (cba_to_ba C)).
    apply (cba_forall_special_case T (fun i: T => cba_implies C m (f i)) j).
    apply cba_forall_is_an_inf; intro j. apply (ba_implies_increasing (cba_to_ba C)).
    simpl. apply cba_forall_special_case.
  Defined.        
  
End the_complete_case.
