# LibraChain

A library providing mechanized proofs of the LibraBFT consensus using the [Coq
theorem prover](https://coq.inria.fr/).


## Architecture & Evolution

This library uses the [SSreflect proof language](https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html) and [mathematical components libraries](https://github.com/math-comp/math-comp) for Coq.

It is compatible with, inspired by, and extends, the [ToyChain
library](https://github.com/certichain/toychain) by George Pirlea, Ilya Sergey
et al.

This library is at an experimental stage and its contents may know significant
evolutions in the future.


## References

### Libra Technical Papers
* [The Libra Blockchain](https://developers.libra.org/docs/the-libra-blockchain-paper)
* [State Machine Replication in the Libra Blockchain](https://developers.libra.org/docs/state-machine-replication-paper)

### HotStuff technical Papers

LibraBFT, studied here, is a Hotstuff-inspired protocol.

* [PODC paper](https://dl.acm.org/doi/abs/10.1145/3293611.3331591)
* [ArXiV full version](https://arxiv.org/abs/1803.05069)

### Versions of the Libra Consensus Papers

Due to the high level of precision requires for a formalized proof,
consultation of both LibraBFT v2 & v3 is recommended:

* [LibraBFT v2](https://developers.libra.org/docs/assets/papers/libra-consensus-state-machine-replication-in-the-libra-blockchain/2019-10-24.pdf)
* [LibraBFT v3](https://developers.libra.org/docs/assets/papers/libra-consensus-state-machine-replication-in-the-libra-blockchain/2020-04-09.pdf)

### Coq libraries used in this development

* [SSReflect](https://hal.inria.fr/inria-00258384)
* [ToyChain master's thesis of George
  Pirlea](https://pirlea.net/papers/toychain-thesis.pdf)
* [Mechanizing BlockChain consensus](https://ilyasergey.net/papers/toychain-cpp18.pdf)

## LICENSE
LibraChain is Apache-2.0 licensed, as found in the [LICENSE](https://github.com/calibra/LibraChain/blob/master/LICENSE) file.
