(*
  This file is part of the verified smart contract project of SECBIT Labs.

  Copyright 2018 SECBIT Labs

  This program is free software: you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public License
  as published by the Free Software Foundation, either version 3 of
  the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public License
  along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

Require Import Arith.
Require Import Nat.
Require Import String.
Open Scope string_scope.

(* XXX: shall Model.event and .state be generated from solidity? *)
Require Import Model.

(* All notations are defined in dsl_scope. *)
Delimit Scope dsl_scope with dsl.

(* *************** *)
(* DSL definitions *)
(* *************** *)

(* Definition of the primitive DSL statements *)
Inductive PrimitiveStmt :=
| DSL_require (cond: state -> env -> message -> bool)
| DSL_emit (evt: state -> env -> message -> event)
| DSL_balances_upd_inc (addr: state -> env -> message -> address)
                       (expr: state -> env -> message -> uint256)
| DSL_balances_upd_dec (addr: state -> env -> message -> address)
                       (expr: state -> env -> message -> uint256)
| DSL_balances_upd (addr: state -> env -> message -> address)
                   (expr: state -> env -> message -> uint256)
| DSL_allowed_upd_inc (from: state -> env -> message -> address)
                      (to: state -> env -> message -> address)
                      (expr: state -> env -> message -> uint256)
| DSL_allowed_upd_dec (from: state -> env -> message -> address)
                      (to: state -> env -> message -> address)
                      (expr: state -> env -> message -> uint256)
| DSL_allowed_upd (from: state -> env -> message -> address)
                  (to: state -> env -> message -> address)
                  (expr: state -> env -> message -> uint256)
| DSL_totalSupply_upd (expr: state -> env -> message -> uint256)
| DSL_name_upd (expr: state -> env -> message -> string)
| DSL_decimals_upd (expr: state -> env -> message -> uint8)
| DSL_symbol_upd (expr: state -> env -> message -> string)
| DSL_owner_upd   (expr: state -> env -> message -> address)
| DSL_paused_upd  (expr: state -> env -> message -> bool)
| DSL_return (T: Type) (expr: state -> env -> message -> T)
| DSL_ctor
| DSL_nop.
Arguments DSL_return [T].

(* Definition of DSL statements *)
Inductive Stmt :=
| DSL_prim (stmt: PrimitiveStmt)
| DSL_if (cond: state -> env -> message -> bool) (then_stmt: Stmt) (else_stmt: Stmt)
| DSL_seq (stmt: Stmt) (stmt': Stmt).

(* Result of statement execution *)
Record Result: Type :=
  mk_result {
      ret_st: state;        (* ending state *)
      ret_evts: eventlist;  (* generated events *)
      ret_stopped: bool;    (* does the execution have to stop? *)
    }.
(* Shortcut definition of Result that the execution can continue *)
Definition Next (st: state) (evts: eventlist) : Result :=
  mk_result st evts false.
(* Shortcut definition of Result that the execution has to stop *)
Definition Stop (st: state) (evts: eventlist) : Result :=
  mk_result st evts true.

(* Semantics of the primitive DSL statements *)
Fixpoint dsl_exec_prim
         (stmt: PrimitiveStmt)
         (st0: state)
         (st: state)
         (env: env) (msg: message) (this: address)
         (evts: eventlist): Result :=
  match stmt with
  | DSL_require cond =>
    if cond st env msg then
      Next st evts
    else
      Stop st0 (ev_revert this :: nil)

  | DSL_emit evt =>
    Next st (evts ++ (evt st env msg :: nil))

  | DSL_return expr =>
    Stop st (evts ++ (ev_return _ (expr st env msg) :: nil))

  | DSL_balances_upd_inc addr expr =>
    Next (mk_st (st_symbol st)
                (st_name st)
                (st_decimals st)
                (st_totalSupply st)
                (a2v_upd_inc (st_balances st) (addr st env msg) (expr st env msg))
                (st_allowed st)
                (st_owner st)
                (st_pause st))
         evts

  | DSL_balances_upd_dec addr expr =>
    Next (mk_st (st_symbol st)
                (st_name st)
                (st_decimals st)
                (st_totalSupply st)
                (a2v_upd_dec (st_balances st) (addr st env msg) (expr st env msg))
                (st_allowed st)
                (st_owner st)
                (st_pause st))
         evts

  | DSL_balances_upd addr expr =>
    Next (mk_st (st_symbol st)
                (st_name st)
                (st_decimals st)
                (st_totalSupply st)
                (st_balances st $+ { (addr st env msg) <- (expr st env msg) })
                (st_allowed st)
                (st_owner st)
                (st_pause st))
         evts

  | DSL_allowed_upd_inc from to expr =>
    Next (mk_st (st_symbol st)
                (st_name st)
                (st_decimals st)
                (st_totalSupply st)
                (st_balances st)
                (aa2v_upd_inc (st_allowed st) (from st env msg) (to st env msg) (expr st env msg))
                (st_owner st)
                (st_pause st))
         evts

  | DSL_allowed_upd_dec from to expr =>
    Next (mk_st (st_symbol st)
                (st_name st)
                (st_decimals st)
                (st_totalSupply st)
                (st_balances st)
                (aa2v_upd_dec (st_allowed st) (from st env msg) (to st env msg) (expr st env msg))
                (st_owner st)
                (st_pause st))
         evts

  | DSL_allowed_upd from to expr =>
    Next (mk_st (st_symbol st)
                (st_name st)
                (st_decimals st)
                (st_totalSupply st)
                (st_balances st)
                (aa2v_upd_2 (st_allowed st) (from st env msg) (to st env msg) (expr st env msg))
                (st_owner st)
                (st_pause st))
         evts

  | DSL_totalSupply_upd expr =>
    Next (mk_st (st_symbol st)
                (st_name st)
                (st_decimals st)
                (expr st env msg)
                (st_balances st)
                (st_allowed st)
                (st_owner st)
                (st_pause st))
         evts

  | DSL_name_upd expr =>
    Next (mk_st (st_symbol st)
                (expr st env msg)
                (st_decimals st)
                (st_totalSupply st)
                (st_balances st)
                (st_allowed st)
                (st_owner st)
                (st_pause st))
         evts

  | DSL_decimals_upd expr =>
    Next (mk_st (st_symbol st)
                (st_name st)
                (expr st env msg)
                (st_totalSupply st)
                (st_balances st)
                (st_allowed st)
                (st_owner st)
                (st_pause st))
         evts

  | DSL_symbol_upd expr =>
    Next (mk_st (expr st env msg)
                (st_name st)
                (st_decimals st)
                (st_totalSupply st)
                (st_balances st)
                (st_allowed st)
                (st_owner st)
                (st_pause st))
         evts

  | DSL_owner_upd expr =>
    Next (mk_st (st_symbol st)
                (st_name st)
                (st_decimals st)
                (st_totalSupply st)
                (st_balances st)
                (st_allowed st)
                (expr st env msg)
                (st_pause st))
         evts
     
  | DSL_paused_upd expr =>
        Next (mk_st (st_symbol st)
                (st_name st)
                (st_decimals st)
                (st_totalSupply st)
                (st_balances st)
                (st_allowed st)
                (st_owner st)
                (expr st env msg))
         evts

  | DSL_ctor =>
    Next st
         (evts ++ (ev_constructor (m_sender msg) :: nil))

  | DSL_nop =>
    Next st evts
  end.

(* Semantics of DSL statements *)
Fixpoint dsl_exec
         (stmt: Stmt)
         (st0: state)
         (st: state)
         (env: env) (msg: message) (this: address)
         (evts: eventlist) {struct stmt}: Result :=
  match stmt with
  | DSL_prim stmt' =>
    dsl_exec_prim stmt' st0 st env msg this evts

  | DSL_if cond then_stmt else_stmt =>
    if cond st env msg then
      dsl_exec then_stmt st0 st env msg this evts
    else
      dsl_exec else_stmt st0 st env msg this evts

  | DSL_seq stmt stmt' =>
    match dsl_exec stmt st0 st env msg this evts with
    | mk_result st'' evts'' stopped  =>
      if stopped then
        mk_result st'' evts'' stopped
      else
        dsl_exec stmt' st0 st'' env msg this evts''
    end
  end.

(* ************************************************************** *)
(* Optional notations that makes the DSL syntax close to Solidity *)
(* ************************************************************** *)

(* Notations for state variables (XXX: shall they be generated from solidity?) *)
Notation "'symbol'" :=
  (fun (st: state) (env: env) (msg: message) => st_symbol st) : dsl_scope.

Notation "'name'" :=
  (fun (st: state) (env: env) (msg: message) => st_name st) : dsl_scope.

Notation "'decimals'" :=
  (fun (st: state) (env: env) (msg: message) => st_decimals st) : dsl_scope.

Notation "'totalSupply'" :=
  (fun (st: state) (env: env) (msg: message) => st_totalSupply st) : dsl_scope.

Notation "'balances'" :=
  (fun (st: state) (env: env) (msg: message) => st_balances st) : dsl_scope.

Notation "'balances' '[' addr ']'" :=
  (fun (st: state) (env: env) (msg: message) =>
     ((balances%dsl st env msg) (addr st env msg))) : dsl_scope.

Notation "'allowed'" :=
  (fun (st: state) (env: env) (msg: message) => st_allowed st) : dsl_scope.

Definition dsl_allowed_access (from to: state -> env -> message -> address) :=
  fun (st: state) (env: env) (msg: message) =>
    (allowed%dsl st env msg) ((from st env msg), (to st env msg)).
Notation "'allowed' '[' from ']' '[' to ']'" :=
  (fun (st: state) (env: env) (msg: message) =>
     (allowed%dsl st env msg) ((from st env msg), (to st env msg))) : dsl_scope.

Notation "'paused'" :=
  (fun (st: state) (env: env) (msg: message) =>  st_pause st) : dsl_scope.

Notation "'owner'" :=
  (fun (st: state) (env: env) (msg: message) =>  st_owner st) : dsl_scope.

Notation "'totalSupply'" :=
  (fun (st: state) (env: env) (msg: message) => st_totalSupply st) : dsl_scope.

(* Notations for events (XXX: shall they be generated from solidity?) *)
Notation "'Transfer' '(' from ',' to ',' value ')'" :=
  (fun (st: state) (env: env) (msg: message) =>
     ev_Transfer (m_sender msg) (from st env msg) (to st env msg) (value st env msg))
    (at level 210): dsl_scope.

Notation "'Approval' '(' sender ',' spender ',' value ')'" :=
  (fun (st: state) (env: env) (msg: message) =>
     ev_Approval (m_sender msg) (sender st env msg) (spender st env msg) (value st env msg))
    (at level 210): dsl_scope.

Notation "'OwnershipTransferred' '(' oldOwner ',' newOwner ')'" :=
  (fun (st: state) (env: env) (msg: message) =>
     ev_OwnershipTransferred (oldOwner st env msg) (newOwner st env msg))
    (at level 210): dsl_scope.

Notation "'OwnershipRenounced' '(' oldOwner ')'" :=
  (fun (st: state) (env: env) (msg: message) =>
     ev_OwnershipRenounced (oldOwner st env msg))
    (at level 210): dsl_scope.

Notation "'OwnershipRenounced' '(' oldOwner ')'" :=
  (fun (st: state) (env: env) (msg: message) =>
     ev_OwnershipRenounced (oldOwner st env msg))
    (at level 210): dsl_scope.

Notation "'Pause()'" :=
  (fun (st: state) (env: env) (msg: message) =>
     ev_Pause )
    (at level 210): dsl_scope.

Notation "'Unpause()'" :=
  (fun (st: state) (env: env) (msg: message) =>
     ev_Unpause)
    (at level 210): dsl_scope.


(* Notations for solidity expressions *)
Definition dsl_ge :=
  fun x y (st: state) (env: env) (msg: message) =>
    (negb (ltb (x st env msg) (y st env msg))).
Infix ">=" := dsl_ge : dsl_scope.

Definition dsl_ge_le :=
  fun x y (st: state) (env: env) (msg: message) =>
    (negb (Nat.leb (x st env msg) (y st env msg))).
Infix ">" := dsl_ge_le : dsl_scope.

Definition dsl_lt :=
  fun x y (st: state) (env: env) (msg: message) =>
    ltb (x st env msg) (y st env msg).
Infix "<" := dsl_lt : dsl_scope.

Definition dsl_le :=
  fun x y (st: state) (env: env) (msg: message) =>
    Nat.leb (x st env msg) (y st env msg).
Infix "<=" := dsl_le : dsl_scope.

Definition dsl_eq :=
  fun x y (st: state) (env: env) (msg: message) =>
    (Nat.eqb (x st env msg) (y st env msg)).
Infix "==" := dsl_eq (at level 70): dsl_scope.

Definition dsl_neq :=
  fun x y (st: state) (env: env) (msg: message) =>
    negb (Nat.eqb(x st env msg) (y st env msg)).
Infix "!=" := dsl_neq (at level 70): dsl_scope.

Definition dsl_neg :=
  fun x (st: state) (env: env) (msg: message) =>
    negb (x st env msg).

  
Definition dsl_add  :=
  fun x y (st: state) (env: env) (msg: message) =>
    (x st env msg) + (y st env msg).
Infix "+" := dsl_add : dsl_scope.

Definition dsl_sub :=
  fun x y (st: state) (env: env) (msg: message) =>
    (x st env msg) - (y st env msg).
Infix "-" := dsl_sub : dsl_scope.

Definition dsl_or :=
  fun x y (st: state) (env: env) (msg: message) =>
    (orb (x st env msg) (y st env msg)).
Infix "||" := dsl_or : dsl_scope.

Notation "'msg.sender'" :=
  (fun (st: state) (env: env) (msg: message) =>
     m_sender msg) : dsl_scope.

Definition otrue := true.
Definition ofalse := false.

Notation "'true'" :=
  (fun (st: state) (env: env) (msg: message) => True) : dsl_scope.
Notation "'false'" :=
  (fun (st: state) (env: env) (msg: message) => False) : dsl_scope.

Notation "'require' '(' cond ')'" :=
  (DSL_require cond) (at level 200) : dsl_scope.
Notation "'emit' evt" :=
  (DSL_emit evt) (at level 200) : dsl_scope.
Notation "'balances' '[' addr ']' '+=' expr" :=
  (DSL_balances_upd_inc addr expr) (at level 0) : dsl_scope.
Notation "'balances' '[' addr ']' '-=' expr" :=
  (DSL_balances_upd_dec addr expr) (at level 0) : dsl_scope.
Notation "'balances' '[' addr ']' '=' expr" :=
  (DSL_balances_upd addr expr) (at level 0) : dsl_scope.
Notation "'allowed' '[' from ']' '[' to ']' '+=' expr" :=
  (DSL_allowed_upd_inc from to expr) (at level 0) : dsl_scope.
Notation "'allowed' '[' from ']' '[' to ']' '-=' expr" :=
  (DSL_allowed_upd_dec from to expr) (at level 0) : dsl_scope.
Notation "'allowed' '[' from ']' '[' to ']' '=' expr" :=
  (DSL_allowed_upd from to expr) (at level 0) : dsl_scope.
Notation "'totalSupply' '=' expr" :=
  (DSL_totalSupply_upd expr) (at level 0) : dsl_scope.
Notation "'symbol' '=' expr" :=
  (DSL_symbol_upd expr) (at level 0) : dsl_scope.
Notation "'name' '=' expr" :=
  (DSL_name_upd expr) (at level 0) : dsl_scope.
Notation "'decimals' '=' expr" :=
  (DSL_decimals_upd expr) (at level 0) : dsl_scope.
Notation "'owner' '=' expr" :=
  (DSL_owner_upd expr) (at level 0) : dsl_scope.
Notation "'paused' '=' expr" :=
  (DSL_paused_upd expr) (at level 0) : dsl_scope.
Notation "'return' expr" :=
  (DSL_return expr) (at level 200) : dsl_scope.
Notation "'nop'" :=
  (DSL_nop) (at level 200) : dsl_scope.
Notation "'ctor'" :=
  DSL_ctor (at level 200) : dsl_scope.

Notation "@ stmt_prim" :=
  (DSL_prim stmt_prim) (at level 200) : dsl_scope.

Notation "'@if' ( cond ) { stmt0 } 'else' { stmt1 }" :=
  (DSL_if cond stmt0 stmt1) (at level 210) : dsl_scope.

Notation "stmt0 ';' stmt1" :=
  (DSL_seq stmt0 stmt1) (at level 220) : dsl_scope.

Notation "'@uint256' x = expr ; stmt" :=
  (let x: state -> env -> message -> uint256 := expr in stmt)
    (at level 230, x ident) : dsl_scope.

Notation "'@address' x = expr ; stmt" :=
  (let x: state -> env -> message -> address := expr in stmt)
    (at level 230, x ident) : dsl_scope.

Notation "'@uint8' x = expr ; stmt" :=
  (let x: state -> env -> message -> uint8 := expr in stmt)
    (at level 230, x ident) : dsl_scope.

Notation "'@string' x = expr ; stmt" :=
  (let x: state -> env -> message -> string := expr in stmt)
    (at level 230, x ident) : dsl_scope.


(* *************************************************************** *)
(* Each section below represents a ERC20 function in DSL and prove *)
(* the DSL representation does implement the specification.        *)
(* *************************************************************** *)

Require Import Spec.

Section dsl_transfer_from.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{from: state -> env -> message -> address}.
  Context `{_from: address}.
  Context `{to: state -> env -> message -> address}.
  Context `{_to: address}.
  Context `{value: state -> env -> message -> uint256}.
  Context `{_value: uint256}.

  Context `{max_uint256: state -> env -> message -> uint256}.
  Context `{zero_address: state -> env -> message -> address}.

  (* Arguments are immutable, generated from solidity *)
  Context `{from_immutable: forall st env msg, from st env msg = _from}.
  Context `{to_immutable: forall st env msg, to st env msg = _to}.
  Context `{value_immutable: forall st env msg, value st env msg = _value}.
  Context `{max_uint256_immutable: forall st env msg, max_uint256 st env msg = MAX_UINT256}.
  Context `{zero_address_immutable: forall st env msg, zero_address st env msg = 0}.

  (* DSL representation of transferFrom(), generated from solidity *)
  Definition transferFrom_dsl : Stmt :=
    (@uint256 allowance = allowed[from][msg.sender] ;
     @require(dsl_neg paused);
     @require(to != zero_address);   
     @require(balances[from] >= value) ;
     @require((balances[to] <= max_uint256 - value)) ;
     @require(allowance >= value) ;
     @balances[from] -= value ;
     @balances[to] += value;
     @allowed[from][msg.sender] -= value;
     (@emit Transfer(from, to, value)) ;
     (@return true)).

  (* Auxiliary lemmas *)
  Lemma nat_nooverflow_dsl_nooverflow:
    forall (m: state -> a2v) st env msg,
      (_from = _to \/ (_from <> _to /\ (m st _to <= MAX_UINT256 - _value)))%nat ->
      ((from == to) ||
       ((fun st env msg => m st (to st env msg)) <= max_uint256 - value))%dsl st env msg = otrue.
  Proof.
    intros m st env msg Hnat.

    unfold "=="%dsl, "<="%dsl, "||"%dsl, "||"%bool, "-"%dsl.
    rewrite (from_immutable st env msg),
            (to_immutable st env msg),
            (value_immutable st env msg),
            (max_uint256_immutable st env msg).
    destruct Hnat.
    - rewrite H. rewrite (Nat.eqb_refl _). reflexivity.
    - destruct H as [Hneq Hle].
      apply Nat.eqb_neq in Hneq. rewrite Hneq.
      apply Nat.leb_le in Hle. exact Hle.
  Qed.

    Lemma transferFrom_cond_dec:
    forall st,
      Decidable.decidable
        (_from = _to \/ _from <> _to /\ (st_balances st _to <= MAX_UINT256 - _value)%nat).
  Proof.
    intros.
    apply Decidable.dec_or.
    - apply Nat.eq_decidable.
    - apply Decidable.dec_and.
      + apply neq_decidable.
      + apply Nat.le_decidable.
  Qed.

  (* Manually proved *)
  Lemma transferFrom_dsl_sat_spec:
    forall st env msg this,
      spec_require (funcspec_transferFrom _from _to _value this env msg) st ->
      forall st0 result,
        dsl_exec transferFrom_dsl st0 st env msg this nil = result ->
        spec_trans (funcspec_transferFrom _from _to _value this env msg) st (ret_st result) /\
        spec_events (funcspec_transferFrom _from _to _value this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st env msg this Hreq st0 result Hexec.
    simpl in Hreq.
    destruct Hreq as [Hreq_pause [Hreq_blncs_lo [Hreq_blncs_hi [Hreq_allwd_hi Hreq_allwd_lo]]]].
    apply Nat.leb_le in Hreq_blncs_hi.
    apply Nat.leb_le in Hreq_allwd_lo.
    apply Nat.leb_le in Hreq_allwd_hi.

    simpl in Hexec.
    unfold dsl_neg in Hexec.
    rewrite Hreq_pause in Hexec.
    simpl in Hexec.
    
    unfold "!="%dsl in Hexec.
    rewrite zero_address_immutable in Hexec.
    rewrite to_immutable in Hexec.
    apply Nat.eqb_neq in  Hreq_blncs_lo.
    rewrite Hreq_blncs_lo in Hexec.
    simpl in Hexec.

    unfold ">="%dsl in Hexec.
    rewrite from_immutable with st env msg in Hexec.
    
    rewrite (Nat.ltb_antisym _ _) in Hexec.
    rewrite (value_immutable _ _ _) in Hexec.
    rewrite Hreq_blncs_hi in Hexec.
    simpl in Hexec.

    unfold "<="%dsl in Hexec.
    rewrite to_immutable in Hexec.
    unfold "-"%dsl in Hexec.
    rewrite  (max_uint256_immutable  _ _ _) in Hexec.
    rewrite (value_immutable _ _ _) in Hexec.
    rewrite Hreq_allwd_hi in Hexec.

    simpl in Hexec.
    rewrite (from_immutable _ _ _) in Hexec.
    rewrite (value_immutable _ _ _) in Hexec.
    rewrite (Nat.ltb_antisym _ _) in Hexec.
    rewrite Hreq_allwd_lo in Hexec.
    simpl in Hexec.

    rewrite (from_immutable _ _ _) in Hexec.
    rewrite (value_immutable _ _ _) in Hexec.
    rewrite (to_immutable _ _ _) in Hexec.
    simpl in Hexec.

    unfold funcspec_transferFrom.
    rewrite <- Hexec.
    simpl.
    repeat rewrite (to_immutable _ _ _).
    repeat rewrite (value_immutable _ _ _).
    repeat rewrite (from_immutable _ _ _).
    repeat (split; auto).
  Qed.

    (* If no require can be satisfied, transferFrom() must revert to the initial state *)
  Lemma transferFrom_dsl_revert:
    forall st env msg this,
      m_func msg = mc_transferFrom _from _to _value ->
      ~ spec_require (funcspec_transferFrom _from _to _value this env msg) st ->
      (forall addr0 addr1, (st_allowed st (addr0, addr1) <= MAX_UINT256)%nat) ->
      forall st0 result,
        dsl_exec transferFrom_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    unfold funcspec_transferFrom, ">="%nat.
    intros st env msg this Hfunc Hreq_neg Hallwd_inv st0 result Hexec;
    simpl in Hreq_neg.

    assert (Hreq_impl:
              ((st_pause st) = ofalse) ->
              ( _to <> 0) ->
              (_value <= st_balances st _from)%nat ->
              (st_balances st _to <= MAX_UINT256 - _value)%nat ->
              ~(_value <= st_allowed st (_from, m_sender msg))%nat).
    {
      intros Hpause Hto Hvalue.
      apply Decidable.or_not_l_iff_1.
      - unfold Decidable.decidable.
        destruct (le_dec (st_balances st _to) ( MAX_UINT256 - _value)).
        left. auto.
        right. auto.
      - generalize Hvalue; clear Hvalue.
        apply Decidable.or_not_l_iff_1.
        + unfold Decidable.decidable.
          destruct (le_dec _value (st_balances st _from)).
          left. auto. right. auto.
        + generalize Hto; clear Hto.
          apply Decidable.or_not_l_iff_1.
          * unfold Decidable.decidable.
            destruct (beq_dec _to 0).
            right. apply Nat.eq_dne.  simplbeq. auto.
            left. apply Nat.eqb_neq in H. auto.
          * generalize Hpause; clear Hpause.
            {apply Decidable.or_not_l_iff_1.
             - apply beq_decidable.
             - apply Decidable.not_and in Hreq_neg.
               + destruct Hreq_neg.
                 left; auto.
                 right. apply Decidable.not_and in H.
                  * destruct H.
                    left; auto.
                     right.
                        { apply Decidable.not_and in H.
                          destruct H.
                          - left. unfold not in H. auto.
                          - apply Decidable.not_and in H.
                            destruct H.
                            + right. left. unfold not in H. auto.
                            + right. right. unfold not in H. auto.
                            + unfold Decidable.decidable.
                              destruct (le_dec (st_balances st _to) (MAX_UINT256 - _value)).
                              left. auto. right. auto.
                          - unfold Decidable.decidable.
                              destruct (le_dec _value (st_balances st _from)).
                              left. auto. right. auto.
                        }
                   * unfold Decidable.decidable.
                     destruct (beq_dec _to 0).
                     right. apply Nat.eq_dne.  simplbeq. auto.
                     left. apply Nat.eqb_neq in H0. auto.
              + apply beq_decidable.
            }
    }
    clear Hreq_neg.
    
    simpl in Hexec.
    unfold dsl_neg in Hexec.
    
    destruct (bool_dec (st_pause st) ofalse).
    + (* st_pause st = false*)
      rewrite e in Hexec. simpl in Hexec.
      unfold "!="%dsl in Hexec.
      rewrite (to_immutable _ _ _) in Hexec.
      rewrite (zero_address_immutable _ _ _) in Hexec.
      destruct (beq_dec _to 0).
      - (* _to = 0 *)
        apply Nat.eqb_eq in H. rewrite H in Hexec.
        simpl in Hexec.
        rewrite <- Hexec. unfold Stop. auto.
      - (* _to <> 0 *)
        apply Nat.eqb_neq in H.
        apply Nat.eqb_neq in H.
        rewrite H in Hexec.
        simpl in Hexec.
        unfold ">="%dsl in Hexec.
        rewrite (from_immutable _ _ _) in Hexec.
        rewrite (value_immutable _ _ _) in Hexec.
        destruct (lt_dec (st_balances st _from) _value).
        * (* balances[from] < value *)
          Print Nat.
          apply Nat.ltb_lt in l.
          rewrite l in Hexec.
          simpl in Hexec.
          rewrite <- Hexec.
          split; auto.        
        * (* balances[from] >= value *)
          apply Nat.ltb_nlt in n.
          rewrite n in Hexec.
          simpl in Hexec.
          unfold "<="%dsl in Hexec.
          rewrite (to_immutable _ _ _) in Hexec.
          unfold "-"%dsl in Hexec.
          rewrite (max_uint256_immutable _ _ _) in Hexec.
          rewrite (value_immutable _ _ _) in Hexec.
                
          destruct (le_dec (st_balances st _to)  (MAX_UINT256 - _value)).
          {(* st_balances st _to <= MAX_UINT256 - _value*)
            apply Nat.leb_le in l.
            rewrite l in Hexec.
            simpl in Hexec.
            rewrite (from_immutable _ _ _) in Hexec.
            rewrite (value_immutable _ _ _) in Hexec.
            apply Nat.eqb_neq in H.
            apply Nat.ltb_nlt in n.

            apply Nat.nlt_ge in n.
            apply Nat.leb_le in l.
            generalize (Hreq_impl e H n l); clear Hreq_impl; intros Hreq_impl.
            apply Nat.leb_nle in Hreq_impl.
            rewrite Nat.leb_antisym in Hreq_impl.
            rewrite Hreq_impl in Hexec.
            simpl in Hexec.
            rewrite <- Hexec.
            unfold Stop. auto.
          }
          {
            Print Nat.
            apply Nat.leb_nle in n0.
            rewrite n0 in Hexec.
            simpl in Hexec.
            rewrite <- Hexec.
            unfold Stop. auto.
          }
        + apply not_false_is_true in n.
          simpl in Hexec.
          unfold "!="%dsl in Hexec.
          rewrite n in Hexec; simpl in Hexec.
          rewrite <- Hexec.
          split; auto.
  Qed.
  
  Close Scope dsl_scope.
End dsl_transfer_from.

Section dsl_transfer.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{to: state -> env -> message -> address}.
  Context `{_to: address}.
  Context `{value: state -> env -> message -> uint256}.
  Context `{_value: uint256}.
  Context `{max_uint256: state -> env -> message -> uint256}.
  Context `{zero_address: state -> env -> message -> address}.

  (* Arguments are immutable, generated from solidity *)
  Context `{to_immutable: forall st env msg, to st env msg = _to}.
  Context `{value_immutable: forall st env msg, value st env msg = _value}.
  Context `{max_uint256_immutable: forall st env msg, max_uint256 st env msg = MAX_UINT256}.
  Context `{zero_address_immutable: forall st env msg, zero_address st env msg = 0}.

  (* DSL representation of transfer(), generated from solidity *)
  Definition transfer_dsl : Stmt :=
    (@require(dsl_neg paused);
     @require(to != zero_address);   
     @require(balances[msg.sender] >= value) ;
     @require(balances[to] <= max_uint256 - value) ;
     @balances[msg.sender] -= value ;
     @balances[to] += value ;
     (@emit Transfer(msg.sender, to, value)) ;
     (@return true)
    ).

  (* Auxiliary lemmas *)
  Lemma nat_nooverflow_dsl_nooverflow':
    forall (m: state -> a2v) st env msg,
      (m_sender msg = _to \/ (m_sender msg <> _to /\ (m st _to <= MAX_UINT256 - _value)))%nat ->
      ((msg.sender == to) ||
       ((fun st env msg => m st (to st env msg)) <= max_uint256 - value))%dsl st env msg = otrue.
  Proof.
    intros m st env msg Hnat.

    unfold "||"%dsl, "||"%bool, "=="%dsl, "<="%dsl, "-"%dsl.
    rewrite (to_immutable st env msg),
            (max_uint256_immutable st env msg),
            (value_immutable st env msg).

    destruct Hnat.
    - rewrite H. rewrite (Nat.eqb_refl _). reflexivity.
    - destruct H as [Hneq Hle].
      apply Nat.eqb_neq in Hneq. rewrite Hneq.
      apply Nat.leb_le in Hle. exact Hle.
  Qed.

  (* Manually proved *)
  Lemma transfer_dsl_sat_spec:
    forall st env msg this,
      spec_require (funcspec_transfer _to _value this env msg) st ->
      forall st0 result,
        dsl_exec transfer_dsl st0 st env msg this nil = result ->
        spec_trans (funcspec_transfer _to _value this env msg) st (ret_st result) /\
        spec_events (funcspec_transfer _to _value this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st env msg this Hreq st0 result Hexec.

    unfold funcspec_transfer in Hreq; simpl in Hreq.
    destruct Hreq as [Hreq_paused [Hreq_to [Hreq_blncs_lo Hreq_blncs_hi]]].
    apply Nat.leb_le in Hreq_blncs_lo.
    apply Nat.leb_le in Hreq_blncs_hi.

    simpl in Hexec.
    unfold dsl_neg in Hexec.
    rewrite Hreq_paused in Hexec.
    simpl in Hexec.

    unfold "!="%dsl in Hexec.
    rewrite zero_address_immutable in Hexec.
    rewrite (to_immutable _ _ _) in Hexec.
    apply Nat.eqb_neq in  Hreq_to.
    rewrite Hreq_to in Hexec.
    simpl in Hexec.

    unfold ">="%dsl in Hexec.
    rewrite (Nat.ltb_antisym _ _) in Hexec.
    rewrite (value_immutable _ _ _) in Hexec.
    rewrite Hreq_blncs_lo in Hexec.
    simpl in Hexec.

    unfold "<="%dsl in Hexec.
    rewrite (to_immutable _ _ _) in Hexec.
    unfold "-"%dsl in Hexec.
    rewrite (value_immutable _ _ _) in Hexec.
    rewrite (max_uint256_immutable _ _ _) in Hexec.
    rewrite Hreq_blncs_hi in Hexec.
    simpl in Hexec.

    unfold Stop in Hexec.

    rewrite (value_immutable _ _ _) in Hexec.
    rewrite (to_immutable _ _ _) in Hexec.
    simpl in Hexec.
    
    unfold funcspec_transfer.
    rewrite <- Hexec.
    repeat rewrite (value_immutable _ _ _).
    repeat rewrite (to_immutable _ _ _).
    repeat (split; auto).
  Qed.

 (* If no require can be satisfied, transfer() must revert to the initial state *)
  Lemma transfer_dsl_revert:
    forall st env msg this,
      m_func msg = mc_transfer _to _value ->
      ~ spec_require (funcspec_transfer _to _value this env msg) st ->
      forall st0 result,
        dsl_exec transfer_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    intros st env msg this Hfunc Hreq_neg st0 result Hexec.

    simpl in Hreq_neg.

    assert (Hreq_impl:
              st_pause st = ofalse ->
              ( _to <> 0) ->
              (_value <= st_balances st (m_sender msg))%nat ->
              ~(st_balances st _to <= MAX_UINT256 - _value)%nat).
     {
      intros Hpaused Hto.
      apply Decidable.or_not_l_iff_1.
      - apply Nat.le_decidable.
      - generalize Hpaused; clear Hpaused.
        apply Decidable.or_not_l_iff_1.
        + apply beq_decidable.
        + apply Decidable.not_and in Hreq_neg.
          *{ 
            destruct Hreq_neg.
              - left; auto.
              - right. apply Decidable.not_and in H.
                + destruct H.
                  * (* ~ _to <> 0 *)
                    apply Nat.eqb_neq in Hto.
                    apply Nat.eq_dne in H.
                    rewrite H in Hto. simpl in Hto. inversion Hto.
                  * (* _to <> 0 *)
                    apply Decidable.not_and in H.
                    auto.
                    apply Nat.le_decidable.
                + unfold Decidable.decidable.
                  left. auto.
             }
          * apply beq_decidable.
    }
    clear Hreq_neg.

    simpl in Hexec.
    unfold dsl_neg in Hexec.
    destruct (bool_dec (st_pause st) ofalse).
    - (* paused = false *)
      generalize (Hreq_impl e); clear Hreq_impl; intros Hreq_impl.
      rewrite e in Hexec; simpl in Hexec.

      unfold "!="%dsl in Hexec.
      rewrite (to_immutable _ _ _) in Hexec.
      rewrite (zero_address_immutable _ _ _) in Hexec.
      destruct (beq_dec _to 0).
      + (* _to = 0 *)
        apply Nat.eqb_eq in H. rewrite H in Hexec.
        simpl in Hexec.
        rewrite <- Hexec. unfold Stop. auto.
      + (* _to <> 0 *)
        apply Nat.eqb_neq in H.
         generalize (Hreq_impl H); clear Hreq_impl; intros Hreq_impl.
        apply Nat.eqb_neq in H.
        rewrite H in Hexec.
        simpl in Hexec.
        unfold ">="%dsl in Hexec.
        rewrite (value_immutable _ _ _) in Hexec.
        * destruct (lt_dec (st_balances st (m_sender msg)) _value).
          {(* balances[msg.sender] < value *)
            
            apply Nat.ltb_lt in l.
            rewrite l in Hexec.
            simpl in Hexec.
            rewrite <- Hexec. 
            unfold Stop. auto.
          }
          { (* balances[msg.sender] >= value *)
            apply Nat.ltb_nlt in n.
            rewrite n in Hexec.
            simpl in Hexec.
            unfold "<="%dsl in Hexec.
            unfold "-"%dsl in Hexec.
            rewrite (value_immutable _ _ _) in Hexec.
            rewrite (to_immutable _ _ _) in Hexec.
            rewrite (max_uint256_immutable _ _ _) in Hexec.

            apply Nat.ltb_ge in n.
            generalize (Hreq_impl n); clear Hreq_impl; intros Hreq_impl.
            apply Nat.leb_nle in Hreq_impl.
            rewrite Hreq_impl in Hexec.
            simpl in Hexec.
            rewrite <- Hexec.
            split; auto.
          }
    - (* paused = true *)
      apply not_false_is_true in n.
      rewrite n in Hexec; simpl in Hexec.
      rewrite <- Hexec.
      split; auto.
  Qed.

  Close Scope dsl_scope.
End dsl_transfer.

Section dsl_balanceOf.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ addr: state -> env -> message -> address }.
  Context `{ _addr: address }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ addr_immutable: forall st env msg, addr st env msg = _addr }.

  (* DSL representation of transfer(), generated from solidity *)
  Definition balanceOf_dsl : Stmt :=
    (@return balances[addr]).

  (* Manually proved *)
  Lemma balanceOf_dsl_sat_spec:
    forall st env msg this,
      spec_require (funcspec_balanceOf _addr this env msg) st ->
      forall st0 result,
        dsl_exec balanceOf_dsl st0 st env msg this nil = result ->
        spec_trans (funcspec_balanceOf _addr this env msg) st (ret_st result) /\
        spec_events (funcspec_balanceOf _addr this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st env msg this Hreq st0 result Hexec.

    simpl in Hexec.
    unfold funcspec_balanceOf.
    rewrite <- Hexec.
    rewrite (addr_immutable _ _ _).
    repeat (split; auto).
  Qed.

  (* If no require can be satisfied, balanceOf() must revert to the initial state *)
  Lemma balanceOf_dsl_revert:
    forall st env msg this,
      m_func msg = mc_balanceOf _addr ->
      ~ spec_require (funcspec_balanceOf _addr this env msg) st ->
      forall st0 result,
        dsl_exec balanceOf_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    intros st env msg this _ Hreq_neg st0 result Hexec.
    simpl in Hreq_neg.
    apply (proj1 Decidable.not_true_iff) in Hreq_neg.
    inversion Hreq_neg.
  Qed.

  Close Scope dsl_scope.
End dsl_balanceOf.

Section dsl_approve.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ spender: state -> env -> message -> address }.
  Context `{ _spender: address }.
  Context `{ value: state -> env -> message -> uint256 }.
  Context `{ _value: uint256 }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ spender_immutable: forall st env msg, spender st env msg = _spender }.
  Context `{ value_immutable: forall st env msg, value st env msg = _value }.

  (* DSL representation of approve(), generated from solidity *)
  Definition approve_dsl : Stmt :=
    (@require(dsl_neg paused);
      @allowed[msg.sender][spender] = value ;
     (@emit Approval(msg.sender, spender, value)) ;
     (@return true)
    ).

  (* Manually proved *)
  Lemma approve_dsl_sat_spec:
    forall st env msg this,
      spec_require (funcspec_approve _spender _value this env msg) st ->
      forall st0 result,
        dsl_exec approve_dsl st0 st env msg this nil = result ->
        spec_trans (funcspec_approve _spender _value this env msg) st (ret_st result) /\
        spec_events (funcspec_approve _spender _value this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st env msg this Hreq st0 result Hexec.

    simpl in Hexec.
    simpl in Hreq.
    unfold dsl_neg in Hexec.
    unfold funcspec_approve in *.
    rewrite Hreq in Hexec.
    simpl in Hexec.
    rewrite <- Hexec.
    repeat rewrite (spender_immutable _ _ _).
    repeat rewrite (value_immutable _ _ _).
    repeat (split; auto).
  Qed.

  (* If no require can be satisfied, approve() must revert to the initial state *)
  Lemma approve_dsl_revert:
    forall st env msg this,
      m_func msg = mc_approve _spender _value ->
      ~ spec_require (funcspec_approve _spender _value this env msg) st ->
      forall st0 result,
        dsl_exec approve_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    intros st env msg this Hfunc Hreq_neg st0 result Hexec.

    simpl in Hreq_neg.
    apply not_false_is_true in Hreq_neg.

    simpl in Hexec.
    unfold dsl_neg in Hexec.
    rewrite Hreq_neg in Hexec; simpl in Hexec.

    rewrite <- Hexec.
    split; auto.
  Qed.
 
  Close Scope dsl_scope.
End dsl_approve.

Section dsl_allowance.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ addr: state -> env -> message -> address }.
  Context `{ _addr: address }.
  Context `{ spender: state -> env -> message -> address }.
  Context `{ _spender: address }.

  (* Arguments are immutable, generated from solidity *)
  Context `{ addr_immutable: forall st env msg, addr st env msg = _addr }.
  Context `{ spender_immutable: forall st env msg, spender st env msg = _spender }.

  (* DSL representation of transfer(), generated from solidity *)
  Definition allowance_dsl : Stmt :=
    (@return allowed[addr][spender]).

  (* Manually proved *)
  Lemma allowance_dsl_sat_spec:
    forall st env msg this,
      spec_require (funcspec_allowance _addr _spender this env msg) st ->
      forall st0 result,
        dsl_exec allowance_dsl st0 st env msg this nil = result ->
        spec_trans (funcspec_allowance _addr _spender this env msg) st (ret_st result) /\
        spec_events (funcspec_allowance _addr _spender this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st env msg this Hreq st0 result Hexec.

    simpl in Hexec.
    unfold funcspec_allowance.
    rewrite <- Hexec.
    rewrite (addr_immutable _ _ _).  
    rewrite (spender_immutable _ _ _).
    repeat (split; auto).
  Qed.

  (* If no require can be satisfied, allowance() must revert to the initial state *)
  Lemma allowance_dsl_revert:
    forall st env msg this,
      m_func msg = mc_allowance _addr _spender ->
      ~ spec_require (funcspec_allowance _addr _spender this env msg) st ->
      forall st0 result,
        dsl_exec allowance_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    intros st env msg this Hfunc Hreq_neg st0 result Hexec.
    simpl in Hreq_neg.
    apply (proj1 Decidable.not_true_iff) in Hreq_neg.
    inversion Hreq_neg.
  Qed.
  
  Close Scope dsl_scope.
End dsl_allowance.


Section dsl_increaseApproval.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ spender: state -> env -> message -> address }.
  Context `{ _spender: address }.
  Context `{ addValue: state -> env -> message -> uint256 }.
  Context `{ _addValue: uint256 }.
  Context `{ max_uint256: state -> env -> message -> uint256}.

  (* Arguments are immutable, generated from solidity *)
  Context `{ spender_immutable: forall st env msg, spender st env msg = _spender }.
  Context `{ addValue_immutable: forall st env msg, addValue st env msg = _addValue }.
  Context `{ max_uint256_immutable: forall st env msg, max_uint256 st env msg = MAX_UINT256}.

  (* DSL representation of approve(), generated from solidity *)
  Definition increaseApproval_dsl : Stmt :=
    ( @require(dsl_neg paused);
      @require(allowed[msg.sender][spender]+ addValue <= max_uint256) ;
      @allowed[msg.sender][spender] += addValue ;
     (@emit Approval(msg.sender, spender, allowed[msg.sender][spender])) ;
     (@return true)
    ).

  (* Manually proved *)
  Lemma increaseApproval_dsl_sat_spec:
    forall st env msg this,
      spec_require (funcspec_increaseApproval _spender _addValue this env msg) st ->
      forall st0 result,
        dsl_exec increaseApproval_dsl st0 st env msg this nil = result ->
        spec_trans (funcspec_increaseApproval _spender _addValue this env msg) st (ret_st result) /\
        spec_events (funcspec_increaseApproval _spender _addValue this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st env msg this Hreq st0 result Hexec.
    simpl in Hreq.
    destruct Hreq as [Hreq_pause Hreq_allow].

    apply Nat.leb_le in Hreq_allow.
    simpl in Hexec.
    unfold dsl_neg in Hexec.
    rewrite Hreq_pause in Hexec.
    
    simpl in Hexec.

    unfold "<="%dsl in Hexec.
    unfold "+"%dsl in Hexec.
    rewrite (spender_immutable _ _ _) in Hexec.
    rewrite (addValue_immutable _ _ _) in Hexec.
    rewrite (max_uint256_immutable _ _ _) in Hexec.
    
    rewrite Hreq_allow in Hexec.
    simpl in Hexec.
    rewrite (spender_immutable _ _ _) in Hexec.
    rewrite (addValue_immutable _ _ _) in Hexec.

    unfold Stop in Hexec.
    simpl in Hexec.


    unfold funcspec_increaseApproval.
    simpl.
    rewrite <- Hexec.
    simpl.
    repeat rewrite (spender_immutable _ _ _).
    repeat rewrite (addValue_immutable _ _ _).
    repeat (split; auto).
  Qed.


  (* If no require can be satisfied, increaseApproval() must revert to the initial state *)
  Lemma increaseApproval_dsl_revert:
    forall st env msg this,
      m_func msg = mc_increaseApproval _spender _addValue ->
      ~ spec_require (funcspec_increaseApproval _spender _addValue this env msg) st ->
      forall st0 result,
        dsl_exec increaseApproval_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    intros st env msg this Hfunc Hreq_neg st0 result Hexec.

    apply increaseApproval_value_inrange in Hfunc.
    destruct Hfunc as [_ Hvalue].

    simpl in Hreq_neg.
    assert (Hreq_impl: st_pause st = ofalse ->
                       ~ (st_allowed st (m_sender msg, _spender) + _addValue <= MAX_UINT256)%nat).
    {
      apply Decidable.or_not_l_iff_1.
      - apply beq_decidable.
      -  apply Decidable.not_and in Hreq_neg.
         unfold ofalse. auto.
         Print Decidable.
         apply beq_decidable.
    }
    clear Hreq_neg.

    destruct (bool_dec (st_pause st) ofalse).
    - (* paused == false *)
      generalize (Hreq_impl e); clear Hreq_impl; intros Hreq_impl.
      apply Nat.leb_nle in Hreq_impl.

      simpl in Hexec.
      unfold dsl_neg in Hexec.
      rewrite e in Hexec; simpl in Hexec.

      unfold "<="%dsl, "+"%dsl in Hexec.
      rewrite (spender_immutable _ _ _) in Hexec.
      rewrite (addValue_immutable _ _ _) in Hexec.
      rewrite (max_uint256_immutable _ _ _) in Hexec.
      rewrite Hreq_impl in Hexec.
      simpl in Hexec.
      rewrite <- Hexec.
      split; auto.

    - (* paused == true *)
      apply not_false_is_true in n.
      simpl in Hexec.
      unfold dsl_neg in Hexec.
      rewrite n in Hexec; simpl in Hexec.
      rewrite <- Hexec.
      split; auto.
  Qed.

  Close Scope dsl_scope.
End dsl_increaseApproval.


Section dsl_decreaseApproval.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ spender: state -> env -> message -> address }.
  Context `{ _spender: address }.
  Context `{ subValue: state -> env -> message -> uint256 }.
  Context `{ _subValue: uint256 }.
  Context `{zero_address: state -> env -> message -> address}.


  (* Arguments are immutable, generated from solidity *)
  Context `{ spender_immutable: forall st env msg, spender st env msg = _spender }.
  Context `{ subValue_immutable: forall st env msg, subValue st env msg = _subValue }.
  Context `{zero_address_immutable: forall st env msg, zero_address st env msg = 0}.
  
  (* DSL representation of approve(), generated from solidity *)
  Definition decreaseApproval_dsl : Stmt :=
    ( @require(dsl_neg paused);
      @uint256 oldValue = allowed[msg.sender][spender] ;
      @if (subValue > oldValue) {
         (@allowed[msg.sender][spender] = zero_address)
     } else {
         (@allowed[msg.sender][spender] -= subValue)
     } ;
     (@emit Approval(msg.sender, spender, allowed[msg.sender][spender])) ;
     (@return true)
    ).

  (* Manually proved *)
  Lemma decreaseApproval_dsl_1_sat_spec:
    forall st env msg this,
      spec_require (funcspec_decreaseApproval_1 _spender _subValue this env msg) st ->
      forall st0 result,
        dsl_exec decreaseApproval_dsl st0 st env msg this nil = result ->
        spec_trans (funcspec_decreaseApproval_1 _spender _subValue this env msg) st (ret_st result) /\
        spec_events (funcspec_decreaseApproval_1 _spender _subValue this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st env msg this Hreq st0 result Hexec.
    simpl in Hreq.
    destruct Hreq as [Hreq_pause Hreq_allow].
    
    simpl in Hexec.
    unfold dsl_neg in Hexec.

    rewrite Hreq_pause in Hexec.
    simpl in Hexec.

    unfold ">"%dsl in Hexec.
    rewrite (spender_immutable _ _ _) in Hexec.
    rewrite (zero_address_immutable _ _ _) in Hexec.
    rewrite (subValue_immutable _ _ _) in Hexec.

    apply Nat.ltb_lt in Hreq_allow.
    rewrite Nat.leb_antisym in Hexec.
    rewrite Hreq_allow in Hexec.
    simpl in Hexec.

    unfold Stop in Hexec.
    
    unfold funcspec_decreaseApproval_1.
    simpl.
    rewrite <- Hexec.
    repeat rewrite (spender_immutable _ _ _).
    repeat rewrite (zero_address_immutable _ _ _).
    simpl.
    repeat (split; auto).
    rewrite <- (tmap_get_upd_eq (st_allowed st) (m_sender msg, _spender) 0%nat) at 2.
    auto.
  Qed.

  (* Manually proved *)
  Lemma decreaseApproval_dsl_2_sat_spec:
    forall st env msg this,
      spec_require (funcspec_decreaseApproval_2 _spender _subValue this env msg) st ->
      forall st0 result,
        dsl_exec decreaseApproval_dsl st0 st env msg this nil = result ->
        spec_trans (funcspec_decreaseApproval_2 _spender _subValue this env msg) st (ret_st result) /\
        spec_events (funcspec_decreaseApproval_2 _spender _subValue this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st env msg this Hreq st0 result Hexec.
    simpl in Hreq.
    destruct Hreq as [Hreq_pause Hreq_allow].
    
    simpl in Hexec.
    unfold dsl_neg in Hexec.

    rewrite Hreq_pause in Hexec.
    simpl in Hexec.

    unfold ">"%dsl in Hexec.
    rewrite (subValue_immutable _ _ _) in Hexec.
    rewrite (spender_immutable _ _ _) in Hexec.
    apply Nat.leb_le in Hreq_allow.
    rewrite Hreq_allow in Hexec.
    simpl in Hexec.
    unfold Stop in Hexec.

    unfold funcspec_decreaseApproval_2.
    simpl.
    rewrite <- Hexec.
    repeat rewrite (spender_immutable _ _ _).
    repeat (split; simpl; auto).
  Qed.

  (* If no require can be satisfied, decreaseApproval() must revert to the initial state *)
  Lemma decreaseApproval_dsl_revert:
    forall st env msg this,
      m_func msg = mc_decreaseApproval _spender _subValue ->
      ~ spec_require (funcspec_decreaseApproval_1 _spender _subValue this env msg) st ->
      ~ spec_require (funcspec_decreaseApproval_2 _spender _subValue this env msg) st ->
      forall st0 result,
        dsl_exec decreaseApproval_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    intros st env msg this Hfunc Hreq_1 Hreq_2 st0 result Hexec.

    simpl in Hreq_1.
    assert (Hreq1_impl: st_pause st = ofalse ->
                        ~ (st_allowed st (m_sender msg, _spender) < _subValue)%nat).
    {
      apply Decidable.or_not_l_iff_1.
      - apply beq_decidable.
      - apply (Decidable.not_and _ _ (beq_decidable _ _)) in Hreq_1; auto.
    }
    clear Hreq_1.

    simpl in Hreq_2.
    assert (Hreq2_impl: st_pause st = ofalse ->
                        ~(st_allowed st (m_sender msg, _spender) >= _subValue)%nat).
    {
      apply Decidable.or_not_l_iff_1.
      - apply beq_decidable.
      - apply (Decidable.not_and _ _ (beq_decidable _ _)) in Hreq_2; auto.
    }
    clear Hreq_2.

    destruct (bool_dec (st_pause st) ofalse).

    - (* paused == false *)
      generalize (Hreq1_impl e); clear Hreq1_impl; intros Hreq1_impl.
      generalize (Hreq2_impl e); clear Hreq2_impl; intros Hreq2_impl.

      apply Nat.nlt_ge in Hreq1_impl.
      apply Hreq2_impl in Hreq1_impl.
      inversion Hreq1_impl.

    - (* paused == true *)
      apply not_false_is_true in n.

      simpl in Hexec.
      unfold dsl_neg in Hexec.
      rewrite n in Hexec; simpl in Hexec.

      rewrite <- Hexec.
      split; auto.
  Qed.
  
  Close Scope dsl_scope.
End dsl_decreaseApproval.


Section dsl_transferOwnership.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ newOwner : state -> env -> message -> address }.
  Context `{ _newOwner: address }.
  Context `{ oldOwner : state -> env -> message -> address }.
  Context `{zero_address: state -> env -> message -> address}.
  
   (* Arguments are immutable, generated from solidity *)
  Context `{ newOwner_immutable: forall st env msg, newOwner st env msg = _newOwner }.
  Context `{ oldOwner_immutable: forall st env msg, oldOwner st env msg = m_sender msg }.
  Context `{zero_address_immutable: forall st env msg, zero_address st env msg = 0}.

  Definition transferOwnership_dsl: Stmt :=
    ( @require(oldOwner == owner);
      @require(newOwner != zero_address);
      @owner = newOwner;
      (@emit OwnershipTransferred(owner, newOwner)) 
    ).
  
  (* Manually proved *)
  Lemma transferOwnership_dsl_sat_spec:
      forall st env msg this,
        spec_require (funcspec_transferOwnership _newOwner this env msg) st ->
        forall st0 result,
          dsl_exec transferOwnership_dsl st0 st env msg this nil = result ->
          spec_trans (funcspec_transferOwnership _newOwner this env msg) st (ret_st result) /\
          spec_events (funcspec_transferOwnership _newOwner this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st env msg this Hreq st0 result Hexec.
    simpl in Hexec.
    simpl in Hreq.
    destruct Hreq as [Hreq_sender Hreq_new].
    apply Nat.eqb_neq  in Hreq_new.
    apply Nat.eqb_eq in Hreq_sender.
    
    unfold  "=="%dsl in Hexec.
    rewrite (oldOwner_immutable _ _ _) in Hexec.
    rewrite Hreq_sender in Hexec.
    simpl in Hexec.

    unfold "!="%dsl in Hexec.
    rewrite (zero_address_immutable _ _ _) in Hexec.
    rewrite (newOwner_immutable _ _ _) in Hexec.
    rewrite Hreq_new in Hexec.
    simpl in Hexec.

    rewrite (newOwner_immutable _ _ _) in Hexec.

    unfold Next in Hexec.
    unfold funcspec_transferOwnership.
    simpl.
    rewrite <- Hexec.
    simpl.
    repeat rewrite (newOwner_immutable _ _ _).
    repeat (split; auto).    
  Qed.

(* If no require can be satisfied, approve() must revert to the initial state *)
  Lemma transferOwnership_dsl_revert:
    forall st env msg this,
      m_func msg = mc_OwnershipTransferred _newOwner ->
      ~ spec_require (funcspec_transferOwnership _newOwner this env msg) st ->
      forall st0 result,
        dsl_exec transferOwnership_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    intros st env msg this Hfunc Hreq_neg st0 result Hexec.
    simpl in Hreq_neg.
    apply Decidable.not_and in Hreq_neg.

     assert (Hreq_impl:
               (m_sender msg = st_owner st ->
            (~ _newOwner <> 0))).
    {
      apply Decidable.or_not_l_iff_1; auto.
       apply Nat.eq_decidable.
    }
    clear Hreq_neg.

    simpl in Hexec.
    unfold "=="%dsl in Hexec.
    destruct (beq_dec (oldOwner st env msg) (st_owner st)).
    + apply Nat.eqb_eq in H.
      assert ((oldOwner st env msg =? st_owner st) = otrue).
      unfold otrue. apply Nat.eqb_eq. auto.
      rewrite H0 in Hexec.
      simpl in Hexec.
      rewrite (oldOwner_immutable _ _ _) in H.
      apply Hreq_impl in H.
      apply Nat.eq_dne in H.

      unfold "!="%dsl in Hexec.
      rewrite (zero_address_immutable _ _ _) in Hexec.
      rewrite (newOwner_immutable _ _ _) in Hexec.
      rewrite H in Hexec. simpl in Hexec.
      rewrite <- Hexec.
      split; auto.
    + apply Nat.eqb_neq in H.
      assert ((oldOwner st env msg =? st_owner st) = ofalse).
      unfold ofalse. apply Nat.eqb_neq. auto.
      rewrite H0 in Hexec.
      simpl in Hexec.
      rewrite <- Hexec.
      split; auto.
    + unfold Decidable.decidable.
      destruct (beq_dec ( m_sender msg) (st_owner st)).
      - apply Nat.eqb_eq in H. left. auto.
      - apply Nat.eqb_neq in H. right. auto.
  Qed.
  
  Close Scope dsl_scope.
End dsl_transferOwnership.

Section dsl_renounceOwnership.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ oldOwner : state -> env -> message -> address }.
  Context `{zero_address: state -> env -> message -> address}.
  
   (* Arguments are immutable, generated from solidity *)
  Context `{ oldOwner_immutable: forall st env msg, oldOwner st env msg = m_sender msg }.
  Context `{zero_address_immutable: forall st env msg, zero_address st env msg = 0}.

  Definition OwnershipRenounced_dsl: Stmt :=
    ( @require(oldOwner == owner);
      @owner = zero_address;
      (@emit OwnershipRenounced(owner)) 
    ).
  
  (* Manually proved *)
  Lemma OwnershipRenounced_dsl_sat_spec:
      forall st env msg this,
        spec_require (funcspec_renounceOwnership this env msg) st ->
        forall st0 result,
          dsl_exec OwnershipRenounced_dsl st0 st env msg this nil = result ->
          spec_trans (funcspec_renounceOwnership this env msg) st (ret_st result) /\
          spec_events (funcspec_renounceOwnership this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st env msg this Hreq st0 result Hexec.
    simpl in Hexec.
    simpl in Hreq.
    apply Nat.eqb_eq in Hreq.
    
    unfold  "=="%dsl in Hexec.
    rewrite (oldOwner_immutable _ _ _) in Hexec.
    rewrite Hreq in Hexec.
    simpl in Hexec.

    rewrite (zero_address_immutable _ _ _) in Hexec.
    unfold Next in Hexec.

    unfold funcspec_renounceOwnership.
    simpl.
    rewrite <- Hexec.
    simpl.
    repeat (split; auto).    
  Qed.

(* If no require can be satisfied, approve() must revert to the initial state *)
  Lemma OwnershipRenounced_dsl_revert:
    forall st env msg this,
      m_func msg = mc_renounceOwnership ->
      ~ spec_require (funcspec_renounceOwnership this env msg) st ->
      forall st0 result,
        dsl_exec OwnershipRenounced_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    intros st env msg this Hfunc Hreq_neg st0 result Hexec.
    simpl in Hreq_neg.
    apply Nat.eqb_neq in Hreq_neg.
          
    simpl in Hexec.
    unfold "=="%dsl in Hexec.
    rewrite (oldOwner_immutable _ _ _) in Hexec.
    rewrite Hreq_neg in Hexec.
    simpl in Hexec.
    rewrite <- Hexec.
    unfold Stop. auto.
  Qed.
  
  Close Scope dsl_scope.
End dsl_renounceOwnership.


Section dsl_pause.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{bePaused: state -> env -> message -> bool}.
  Context `{sender : state -> env -> message -> address }.
  
   (* Arguments are immutable, generated from solidity *)
  Context `{bePaused_immutable: forall st env msg, bePaused st env msg = otrue}.
  Context `{ sender_immutable: forall st env msg, sender st env msg = m_sender msg }.

  Definition pause_dsl: Stmt :=
    ( @require(sender == owner);
      @require(dsl_neg paused);
      @paused = bePaused;
      @emit Pause()
    ).
  
  (* Manually proved *)
  Lemma pause_dsl_sat_spec:
      forall st env msg this,
        spec_require (funcspec_pause this env msg) st ->
        forall st0 result,
          dsl_exec pause_dsl st0 st env msg this nil = result ->
          spec_trans (funcspec_pause this env msg) st (ret_st result) /\
          spec_events (funcspec_pause this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st env msg this Hreq st0 result Hexec.
    simpl in Hexec.
    simpl in Hreq.
    destruct Hreq as [Hreq_owner Hreq_pause].
    apply Nat.eqb_eq in Hreq_owner.
    
    unfold  "=="%dsl in Hexec.
    rewrite (sender_immutable _ _ _) in Hexec.
    rewrite Hreq_owner in Hexec.
    simpl in Hexec.

    unfold dsl_neg in Hexec.
    rewrite Hreq_pause in Hexec.
    simpl in Hexec.
    
    unfold Next in Hexec.

    unfold funcspec_pause.
    simpl.
    rewrite <- Hexec.
    simpl.
    repeat (split; auto).    
  Qed.

  
(* If no require can be satisfied, pause() must revert to the initial state *)
Lemma pause_dsl_revert:
    forall st env msg this,
      m_func msg = mc_pause ->
      ~ spec_require (funcspec_pause this env msg) st ->
      forall st0 result,
        dsl_exec pause_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    intros st env msg this Hfunc Hreq_neg st0 result Hexec.

    simpl in Hreq_neg.    
    assert (Hreq_impl:  st_owner st = m_sender msg -> ~ st_pause st = ofalse).
    {
      apply Decidable.or_not_l_iff_1.
      - unfold Decidable.decidable. 
        destruct (Nat.eq_dec (st_owner st) (m_sender msg)).
        left. auto. right. auto.
      - apply (Decidable.not_and) in Hreq_neg.
        Print Nat.
        unfold ofalse.
        assert (m_sender msg <> st_owner st -> (st_owner st = m_sender msg -> False)).
        apply Nat.neq_sym.
        destruct Hreq_neg.
        left. apply H. auto.
        right. auto.
        unfold Decidable.decidable. 
        destruct (Nat.eq_dec (st_owner st) (m_sender msg)).
        left. auto. right. auto.
    }
    clear Hreq_neg.

    simpl in Hexec. unfold "=="%dsl in Hexec.
    destruct (Nat.eq_dec (st_owner st) (m_sender msg)).
    - (* owner == msg.sender *)
      apply Nat.eq_sym in e. 
      apply Nat.eqb_eq in e.
      rewrite (sender_immutable _ _ _) in Hexec. 
      rewrite e in Hexec; simpl in Hexec.

      unfold dsl_neg in Hexec.
      apply Nat.eqb_eq in e.
      apply Nat.eq_sym in e.
      apply Hreq_impl in e.

      unfold ofalse in e.

      apply not_false_is_true in e.
      rewrite e in Hexec.
      simpl in Hexec.

      rewrite <- Hexec.
      unfold Stop. auto.
    - (* owner <> msg.sender *)
      
      rewrite (sender_immutable _ _ _) in Hexec.
      apply Nat.neq_sym in n.
      apply Nat.eqb_neq in n.     
      rewrite n in Hexec.
      simpl in Hexec.
      rewrite <- Hexec.
      unfold Stop. auto.
  Qed.

  Close Scope dsl_scope.
End dsl_pause.

Section dsl_unpause.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{notPaused: state -> env -> message -> bool}.
  Context `{sender : state -> env -> message -> address }.
  
   (* Arguments are immutable, generated from solidity *)
  Context `{notPaused_immutable: forall st env msg, notPaused st env msg = ofalse}.
  Context `{ sender_immutable: forall st env msg, sender st env msg = m_sender msg }.

  Definition unpause_dsl: Stmt :=
    ( @require(sender == owner);
      @require(paused);
      @paused = notPaused;
      @emit Pause()
    ).
  
  (* Manually proved *)
  Lemma unpause_dsl_sat_spec:
      forall st env msg this,
        spec_require (funcspec_unpause this env msg) st ->
        forall st0 result,
          dsl_exec unpause_dsl st0 st env msg this nil = result ->
          spec_trans (funcspec_unpause this env msg) st (ret_st result) /\
          spec_events (funcspec_unpause this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st env msg this Hreq st0 result Hexec.
    simpl in Hexec.
    simpl in Hreq.
    destruct Hreq as [Hreq_owner Hreq_pause].
    apply Nat.eqb_eq in Hreq_owner.
    
    unfold  "=="%dsl in Hexec.
    rewrite (sender_immutable _ _ _) in Hexec.
    rewrite Hreq_owner in Hexec.
    simpl in Hexec.

    rewrite Hreq_pause in Hexec.
    simpl in Hexec.
    
    unfold Next in Hexec.

    unfold funcspec_unpause.
    simpl.
    rewrite <- Hexec.
    simpl.
    repeat rewrite (notPaused_immutable _ _ _).
    repeat (split; auto).    
  Qed.

(* If no require can be satisfied, pause() must revert to the initial state *)
Lemma unpause_dsl_revert:
    forall st env msg this,
      m_func msg = mc_pause ->
      ~ spec_require (funcspec_unpause this env msg) st ->
      forall st0 result,
        dsl_exec unpause_dsl st0 st env msg this nil = result ->
        result = Stop st0 (ev_revert this :: nil).
  Proof.
    intros st env msg this Hfunc Hreq_neg st0 result Hexec.

    simpl in Hreq_neg.    
    assert (Hreq_impl:  st_owner st = m_sender msg -> ~ st_pause st = otrue).
    {
      apply Decidable.or_not_l_iff_1.
      - unfold Decidable.decidable. 
        destruct (Nat.eq_dec (st_owner st) (m_sender msg)).
        left. auto. right. auto.
      - apply (Decidable.not_and) in Hreq_neg.
        unfold otrue.
        assert (m_sender msg <> st_owner st -> (st_owner st = m_sender msg -> False)).
        apply Nat.neq_sym.
        destruct Hreq_neg.
        left. apply H. auto.
        right. auto.
        unfold Decidable.decidable. 
        destruct (Nat.eq_dec (st_owner st) (m_sender msg)).
        left. auto. right. auto.
    }
    clear Hreq_neg.

    simpl in Hexec. unfold "=="%dsl in Hexec.
    destruct (Nat.eq_dec (st_owner st) (m_sender msg)).
    - (* owner == msg.sender *)
      apply Nat.eq_sym in e. 
      apply Nat.eqb_eq in e.
      rewrite (sender_immutable _ _ _) in Hexec. 
      rewrite e in Hexec; simpl in Hexec.

      unfold dsl_neg in Hexec.
      apply Nat.eqb_eq in e.
      apply Nat.eq_sym in e.
      apply Hreq_impl in e.

      unfold otrue in e.

      apply not_true_is_false in e.
      rewrite e in Hexec.
      simpl in Hexec.

      rewrite <- Hexec.
      unfold Stop. auto.
    - (* owner <> msg.sender *)
      
      rewrite (sender_immutable _ _ _) in Hexec.
      apply Nat.neq_sym in n.
      apply Nat.eqb_neq in n.     
      rewrite n in Hexec.
      simpl in Hexec.
      rewrite <- Hexec.
      unfold Stop. auto.
  Qed.
  
  Close Scope dsl_scope.
End dsl_unpause.

    
Section dsl_constructor.
  Open Scope dsl_scope.

  (* Declare arguments, generated from solidity *)
  Context `{ initialAmount : state -> env -> message -> uint256 }.
  Context `{ ownerAddress : state -> env -> message -> address }.
  Context `{zero_address: state -> env -> message -> address}.


  (* Arguments are immutable, generated from solidity *)
  Context `{ initialAmount_immutable: forall st env msg, initialAmount st env msg = INITIAL_SUPPLY }.
  Context `{ ownerAddress_immutable: forall st env msg, ownerAddress st env msg = m_sender msg }.
  Context `{zero_address_immutable: forall st env msg, zero_address st env msg = 0}.
  
  (* DSL representation of constructor, generated from solidity *)
  Definition ctor_dsl : Stmt :=
    (@balances[msg.sender] = initialAmount ;
     @totalSupply = initialAmount ;
     @DSL_owner_upd ownerAddress;
     @ctor;
     (@emit Transfer(zero_address ,msg.sender, initialAmount)) 
    ).

  (* Manually proved *)
  Lemma ctor_dsl_sat_spec:
    forall st,
      st_balances st = $0 ->
      st_allowed st = $0 ->
      forall env msg this,
        spec_require (funcspec_constructor this env msg) st ->
        forall st0 result,
          dsl_exec ctor_dsl st0 st env msg this nil = result ->
          spec_trans (funcspec_constructor this env msg) st (ret_st result) /\
          spec_events (funcspec_constructor this env msg) (ret_st result) (ret_evts result).
  Proof.
    intros st Hblns_init Hallwd_init env msg this Hreq st0 result Hexec.

    simpl in Hexec.
    unfold Next in Hexec.
    
    unfold funcspec_constructor.
    rewrite <- Hexec.
    simpl.
    rewrite Hblns_init.
    rewrite Hallwd_init.
    repeat rewrite (initialAmount_immutable _ _ _).
    repeat rewrite (ownerAddress_immutable _ _ _).
    repeat rewrite (zero_address_immutable _ _ _).
    repeat (split; auto).
  Qed.
  
  Close Scope dsl_scope.
End dsl_constructor.