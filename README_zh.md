# Calculus Token with Proof

[English Version](README.md)

该仓库包含对以太坊 Token 合约 *calculus* 的形式化证明。全部证明在交互式证明辅助工具 [Coq](https://coq.inria.fr/) 中完成。

## 合约基本信息

* Token 名称： **Calculus Token**
* Token 符号： CAL
* 合约地址： [```0xf67a0910a341800b7446554102344c43883d9c78```](https://etherscan.io/address/0xf67a0910a341800b7446554102344c43883d9c78)
* 项目网站： [Calculus](http://www.calculus.network/)

## 证明内容

我们证明了该合约具备以下性质。这些性质组成了该合约的正确性定义。

1. [```Property_totalSupply_equal_to_sum_balances```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L993) Token 总供应量始终和所有账户中的 Token 数量的总和相等。

2. [```Property_totalSupply_fixed_transfer```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1010) Token 总供应量不受 ```transfer()``` 函数影响。

3. [```Property_totalSupply_fixed_after_initialization```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1120) 合约部署后，Token 总供应量永远不会改变。

4. [```Property_totalSupply_fixed_delegate_transfer```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1134) Token 总供应量不受 ```transferFrom()``` 函数影响。

5. [```Property_from_to_balances_change```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1148) ```transfer()``` 函数只会从调用者的账户转移指定数量的 Token 到指定的接受者的账户中。

6. [```Property_pause_only_by_owner```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1191) 只有 Token 合约所有者可以暂停合约。

7. [```Property_unpause_only_by_owner```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1209) 只有 Token 合约所有者可以继续合约的执行。

8. [```Property_restricted_owner_for_transfer```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1227) Token 合约所有者不能通过 ```transfer()``` 函数转移任意账户中的 Token。

9. [```Property_restricted_owner_for_transferFrom```](https://github.com/sec-bit/calculus-token-with-proof/blob/master/proof/Prop.v#L1260) Token 合约所有者不能通过 ```transferFrom()``` 函数转移任意账户中的 Token。

## 证明结构

对该合约的形式化证明由以下几个部分组成。关于证明过程和结构的更加详细的介绍，可以参考  [tokenlibs-with-proofs: Proving Process](https://github.com/sec-bit/tokenlibs-with-proofs/tree/6310c6590aaf664be47342caa3a8854b2447f05e#proving-process)。

* [```Model.v```](proof/Model.v) 定义了合约的模型，对合约的 storage、events、message calls 以及外部环境进行了抽象。

* [```Spec.v```](proof/Spec.v) 定义了合约的规范，形式化描述了合约的每个公共函数的预期行为。

* [```DSL.v```](proof/DSL.v) 在 Coq 中表示了合约的 Solidity 实现，并形式化证明了合约的每个函数的确实现了 [```Spec.v```](proof/Spec.v) 中定义的规范。

* [```Prop.v```](proof/Prop.v) 定义了高层的合约正确性和安全性的性质，并形式化证明了合约的确能够保证这些性质。

## 快速检查证明

该仓库中的所有证明均在交互式定理证明工具 [Coq](https://coq.inria.fr/) 中完成。Coq 可以为证明生成显式的证明项。这些证明项的正确性可以由 Coq 中的一个小证明检查工具检查，并且这个检查过程独立于证明的构造过程。Coq 及其中的证明检查器可以按照 [官方安装指南](https://github.com/coq/coq/wiki#coq-installation) 安装。

安装完成后，可以执行以下命令调用证明检查器检查该仓库中的证明。

``` shell
cd proof; make
```

## 为什么需要形式化证明

与传统的测试和安全审计相比，形式化证明具有以下优点。

1. 通过无二义的数学语言，形式化证明可以*准确*的定义一个合约的正确和安全。

2. 通过严格的数学证明，形式化证明可以*完整*的覆盖合约的所有执行条件和执行路径。
