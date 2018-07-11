
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

Require Export LibEx.
Require Export Lists.List.
Require Export ZArith.
Require Export Integers.
Require Export String.
Require Export Types.
Require Export Mapping.
Require Export AbsModel.

(*
  The state of an fixed-supply ERC20 token contract.

  contract FixedSupplyToken is ERC20Interface, Owned {
    string public symbol;
    string public  name;
    uint8 public decimals;
    uint public _totalSupply;

    mapping(address => uint) balances;
    mapping(address => mapping(address => uint)) allowed;
    ...
  }
*)
Record state : Type :=
  mk_st {
      st_symbol: string;
      st_name: string;
      st_decimals: uint8;
      st_totalSupply: uint256;
      st_balances: a2v;
      st_allowed: aa2v;
      
      st_owner: address;
      st_pause: bool;
   }.

Inductive event : Type :=
  | ev_constructor(a: address): event
  | ev_Transfer (a: address) (from: address) (to: address) (v: value): event
  | ev_Approval (a: address) (owner: address) (spender: address) (v: value): event
  | ev_OwnershipTransferred (owner: address)(newOwner: address): event                                                                             
  | ev_OwnershipRenounced (owner: address): event
  | ev_Pause: event
  | ev_Unpause: event
  | ev_return (A: Type) (ret: A) : event
  | ev_revert (this: address):event
.

Definition eventlist := TEventList event.

Definition env := TEnv.

Definition contract := TContract state.

(* Method call *)
Inductive mcall : Type :=
  | mc_constructor: mcall
  | mc_totalSupply: mcall                  
  | mc_balanceOf (owner: address): mcall
  | mc_transfer (to: address) (v: value): mcall
  | mc_transferFrom (from: address) (to: address) (v: value): mcall
  | mc_approve (spender: address) (v: value): mcall
  | mc_allowance (owner: address) (spender: value): mcall
  | mc_increaseApproval (spender: address)(addValue: value): mcall
  | mc_decreaseApproval (spender: address)(subValue: value): mcall
  | mc_OwnershipTransferred (newOwner: address): mcall                                                                            
  | mc_renounceOwnership: mcall                                                             
  | mc_pause: mcall
  | mc_unpause: mcall
.

(* Message, with a simplication that args are embedded in `m_func`,
   instead of calldata *)
Definition message := TMessage mcall.
