SBVR SE Parsing Engine
======================
This is a fork of APE (ACE Parsing Engine) made to parse SBVR Structured English sentences,
especially rules. The goal is to support Deontic and Alethic statements.

In particular, the following kinds of sentences are supported:

1. Regulative statements:
   1. It is obligatory that
   1. It is prohibited that
   1. It is permitted that
1. Constitutive statements:
   1. It is necessary that
   1. It is possible that
   1. It is impossible that

What is different from Attempto?
--------------------------------
Beware that the semantics of sentences produced by this parser differ from the original one, in
particular:

1. DRS for regulative statements (i.e. having deontic modalities) are introduced, namely `obl` and 
   `per`
1. DRS for constitutive statements (i.e. having alethic modalities) are changed from `must` to 
   `nec` and from `can` to `poss`.
1. A prohibition statement produces an obligation DRS that embeds a negation (according to SBVR 
   1.3)
1. An impossibility statements produces a necessity DRS that embeds a negation (according to SBVR
   1.3); Attempto produces a `\neg can` DRS.
1. The following statements are not supported anymore:
   1. It is not possible
   1. It is not necessary
   1. It is recommended
   1. It is not recommended
   1. It is admissible
   1. It is not admissible
1. May and should are both not supported anymore with their respective DRSs.
