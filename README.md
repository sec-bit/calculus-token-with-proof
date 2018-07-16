# Calculus Token with Proof

This repository contains the formal correctness proofs of the Ethereum Token contract *calculus*. All are composed in the interactive proof assistant [Coq](https://coq.inria.fr/).

## Contract information

* Token name: **Calculus Token**
* Token symbol: CAL
* Contract address: [```0xf67a0910a341800b7446554102344c43883d9c78```](https://etherscan.io/address/0xf67a0910a341800b7446554102344c43883d9c78)
* Project website: [Calculus](http://www.calculus.network/)

## What are proved?

The contract is proved to have following properties, which formally define the correctness of this contract.

1. [```Property_totalSupply_equal_to_sum_balances```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L993) the total supply always equals the sum of all balances.

2. [```Property_totalSupply_fixed_transfer```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1010) the total supply is never changed by ```transfer()```.

3. [```Property_totalSupply_fixed_after_initialization```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1120) the total supply is never changed after the contract deployment.

4. [```Property_totalSupply_fixed_delegate_transfer```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1134) the total supply is never changed by ```transferFrom()```.

5. [```Property_from_to_balances_change```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1148) ```transfer()``` always transfers the specified amount tokens from the caller account to the specified receiver's account.

6. [```Property_pause_only_by_owner```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1191) only the token owner can pause the contract.

7. [```Property_unpause_only_by_owner```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1209) only the token owner can unpause the contract.

8. [```Property_restricted_owner_for_transfer```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1227) the token owner cannot transfer tokens in arbitrary accounts by ```transfer()```.

9. [```Property_restricted_owner_for_transferFrom```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1260) the token owner cannot transfer tokens in arbitrary accounts by ```transferFrom()```.

## Proof structure

The proof is composed of following components. A comprehensive introduction of the proving process and structure can be found at [tokenlibs-with-proofs: Proving Process](https://github.com/sec-bit/tokenlibs-with-proofs/tree/6310c6590aaf664be47342caa3a8854b2447f05e#proving-process)

* [```Model.v```](proof/Model.v) defines the contract model, which abstracts the storage, the events, the message calls, and the external environment of this contract.

* [```Spec.v```](proof/Spec.v) defines the contract specification, which formally describes the expected behavior of each public function of this contract.

* [```DSL.v```](proof/DSL.v) expresses the Solidity implementation of this contract in Coq and proves the implementation of each public function does implement the specification in [```Spec.v```](proof/Spec.v).

* [```Prop.v```](proof/Prop.v) formally defines high-level correctness and security properties of this contract and proves the contract specification does guarantee the correctness.

## Quick check the proof

The proof is accomplished in the interactive proof assistant [Coq](https://coq.inria.fr/) **8.7.0**, which can generate explicit proof objects. The proof objects can be checked by a small proof checker provided by Coq in a way independently of the proving process. The proof checker can be installed along with Coq by following the [official instructions](https://github.com/coq/coq/wiki#coq-installation).

After Coq is installed, the proof checked can be called by the following command.

``` shell
cd proof; make
```

## Why the formal proof?

The formal proof has the following benefits over the existing test and security audit.

* By defining in the unambiguous mathematical language, the formal proof can *precisely* define the scope of correctness and security.

* By strict mathematical proving, the formal proof can *fully* cover every case and code path of the smart contract *w.r.t.* the given definitions of formal specification and high-level properties.
