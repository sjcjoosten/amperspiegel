#
# INSTALLATION
# 

The software is tested with GHC-8.0.1 [![Build Status](https://travis-ci.org/sjcjoosten/amperspiegel.svg?branch=master)](https://travis-ci.org/sjcjoosten/amperspiegel)
Newer versions are likely to work too
Installation works via cabal, which comes as part of both
stack and the ghc-package.

To install amperspiegel in your path, run (in the directory of this README):

```
cabal install
```

Alternatively, you can try a manual install using ``ghc --make amperspiegel``
but this will likely complain about missing packages, which you can install via
cabal install. For a list of required packages, check 'build-depends:' in the
amperspiegel.cabal file. The packages base, containers and text are probably
already installed with ghc.

#
# LICENSE
# 

I put a GPL-3 license to get you started on using this software. For the license
see the file LICENSE. I am the only contributer (as of Sept 2016). This means
that if you need a less restrictive license (like BSD / Apache 2.0) you should
just contact me, I'll probably be open to it.

#
# GETTING STARTED
#

Here is a script you may try after installing amperspiegel in your path

{% include demo/demo.sh %}

For an overview of all switches, use:
``
amperspiegel -h
``

#
# Implementation notes
#

A state assigns a population to each variable.
Initially, these are the assignments:
  "parser" gets assigned a population describing the built-in parser
  "asParser" gets assigned that for the built-in ruleList
all other variables get assigned the empty population, in particular:
  "rules", which stands for rules that can be applied to a population
  "population", which stands for the population we're working on currently
    Consequently, most switches get "population" as default argument

The switch -i uses "parser" as a parser to parse each of its arguments  (resulting in a list of populations)
Next, the union over the resulting list of populations is taken         (resulting in a population)
To this population, "rules" is applied as a rule-set                    (resulting in a population)
This result is put in "population" (Resulting in a state)

The switch -asParser applies "asParser" on "population", then filters it.
Consequently, "population" only contains stuff relevant for parser and rules.
It then copies "population" to "parser" and "rules".

Switches -count and -show displays stuff about a variable.
That's it! Not much else is used in this demo.

The switch -apply from below already works. The switch -filter does not.

## Future work
 
See the [issues page](https://github.com/sjcjoosten/amperspiegel/issues?utf8=%E2%9C%93&q=is%3Aopen). 
