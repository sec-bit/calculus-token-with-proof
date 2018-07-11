# Caculus Token with Proof

This repository collects correctness proof of Ethereum token contract *calculas* given specifications and high-level properties. All of them are accomplished in Coq. 

## Contract Info

- token name: **Calculus Token**
- symbol: CAL
- contract address:0xf67a0910a341800b7446554102344c43883d9c78
- website: http://www.calculus.network/

## Requirements

[Coq](https://coq.inria.fr/) is required if you are going to check the correctness of proofs in this repo. [ProofGeneral](https://proofgeneral.github.io/) or CoqIde is required if you are going to read the definitions and the proofs in this repo thoroughly.

### Coq 8.7.0

[Coq](https://coq.inria.fr/) is an interactive proof assistant, which, as its name suggested, assists users to construct proofs. Its also provides a small proof checker that checks the correctness of the proof. It is required if you desire to check the correctness of proofs in this repo.

The definitions and the proofs are implemented in Coq **8.7.0** (other versions may or may not work), which can be installed by following the [official instructions](https://github.com/coq/coq/wiki#coq-installation).

### CoqIde

CoqIde is the official graphic front-end of Coq. It's usually installed along with Coq as shown in the above [Coq installation instructions](https://github.com/coq/coq/wiki#coq-installation). It does not require further configurations after installation. If any, you can refer to the [official instructions](https://github.com/coq/coq/wiki/Configuration%20of%20CoqIDE).

### ProofGeneral

If you are an [Emacs](https://www.gnu.org/software/emacs/) user, a more convenient front-end of Coq is [ProofGeneral](https://proofgeneral.github.io/). The installation instructions of ProofGeneral can be found at https://proofgeneral.github.io/ and https://github.com/ProofGeneral/PG/blob/master/INSTALL.

## Quick Check Proofs

Coq proof checker can be invoked to check whether proofs are correct by the following command,

```shell
make
```

or if you want to check the proof of an individual contract,

```shell
cd proof; make
```

## Repo Structure

```js
Caculus Token with Proof
├── calculus.sol
├── calculus.ysl
├── libs
│   ├── AbsModel.v
│   ├── BNat.v
│   ├── LibEx.v
│   ├── Mapping.v
│   ├── TMap.v
│   ├── TMapLib.v
│   └── Types.v
├── proof
│   ├── DSL.v
│   ├── Makefile
│   ├── Model.v
│   ├── Prop.v
│   ├── Spec.v
│   └── _CoqProject
└── readme.md
```

