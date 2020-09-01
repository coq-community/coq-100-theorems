# 100 famous theorems proved using Coq

[![Travis][travis-shield]][travis-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[travis-shield]: https://travis-ci.com/coq-community/coq100.svg?branch=master
[travis-link]: https://travis-ci.com/coq-community/coq100/builds

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



[Freek Wiedijk's webpage](http://www.cs.ru.nl/~freek/100/) lists
[100 famous theorems](http://pirate.shu.edu/~kahlnath/Top100.html)
and how many of those have been formalised using proof assistants.
This repository keeps track of the statements that have been proved
using the [Coq proof assistant](https://coq.inria.fr/).

You can see the list on [this webpage](https://madiot.fr/coq100).

This repository also contains the proofs of some of the theorems:
- [ballot.v](ballot.v) for the [Ballot Theorem](https://en.wikipedia.org/wiki/Bertrand%27s_ballot_theorem)
- [birthday.v](birthday.v) for the [Birthday Problem](https://en.wikipedia.org/wiki/Birthday_problem)
- [cardan3.v](cardan3.v) for The Solution of a [Cubic](https://en.wikipedia.org/wiki/Cubic_equation)
- [div3.v](div3.v) for [Divisibility by 3 Rule](https://en.wikipedia.org/wiki/Divisibility_rule#Divisibility_by_3_or_9)
- [inclusionexclusion.v](inclusionexclusion.v) for the [Inclusion/Exclusion Principle](https://en.wikipedia.org/wiki/Inclusion%E2%80%93exclusion_principle#Statement)
- [konigsberg_bridges.v](konigsberg_bridges.v) for the [Konigsberg Bridges Problem](https://en.wikipedia.org/wiki/Seven_Bridges_of_K%C3%B6nigsberg)
- [mean.v](mean.v) for the [Arithmetic Mean/Geometric Mean](https://en.wikipedia.org/wiki/Inequality_of_arithmetic_and_geometric_means#The_inequality)
- [sumarith.v](sumarith.v) for [Sum of an arithmetic series](https://en.wikipedia.org/wiki/Arithmetic_progression#Sum)
- [sumkthpowers.v](sumkthpowers.v) for [Sum of kth powers](https://en.wikipedia.org/wiki/Bernoulli_polynomials#Sums_of_pth_powers)

## Meta

- Author(s):
  - Jean-Marie Madiot
  - Frédéric Chardard
- Coq-community maintainer(s):
  - Jean-Marie Madiot ([**@jmadiot**](https://github.com/jmadiot))
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.10 or later
- Additional dependencies:
  - [Coquelicot 3.1.0 or later](http://coquelicot.saclay.inria.fr)
- Coq namespace: `Coq100`
- Related publication(s): none

## Building instructions

To build all theorems that are hosted in this repository,
run the following commands:

``` shell
git clone https://github.com/coq-community/coq100
cd coq100
make   # or make -j <number-of-cores-on-your-machine>
```


