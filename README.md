Current status of the build, including test scripts:
[![Build Status](https://travis-ci.org/sjcjoosten/amperspiegel.svg?branch=master)](https://travis-ci.org/sjcjoosten/amperspiegel)

#
# INSTALLATION
# 

The software is tested with GHC-8.0.1.
Newer versions are likely to work too.
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

I put a GPL-3 license to get you started on using and modifying this software.
For the license see the file LICENSE.
Since I am the only contributer, you can ask me for a less restrictive license (like BSD / Apache 2.0) if you need one.
I'll probably be open to giving it to you.

#
# GETTING STARTED
#

[Here is a script you may try after installing amperspiegel in your path](demo/demo.sh)

For an overview of all switches, use:
``
amperspiegel -h
``

After having done all this, send me an email (or a message in github, or ..) and tell me what you think. I like knowing who is trying out my software. Don't be shy: I'll remove this notice once I'm getting too many such emails.

#
# Implementation notes
#

A state assigns a population to each variable.
Initially, these are the assignments:

 - "parser" gets assigned a population describing the built-in parser
 - "asParser" gets assigned that for the built-in ruleList
 - possibly some others, use -list to see them

All other variables get assigned the empty population by default, the following in particular:

  - "rules", which stands for rules that can be applied to a population
  - "population", which stands for the population we're working on currently
    Consequently, most switches get "population" as default argument

The switch -i uses "parser" as a parser to parse each of its arguments
Next, the union over the resulting list of populations is taken
To this population, "rules" is applied as a rule-set
This result is put in "population" (Resulting in a state)

The switch -asParser applies "asParser" on "population", then filters it.
Consequently, "population" only contains stuff relevant for parser and rules.
It then copies "population" to "parser" and "rules".

Switches -count and -show displays stuff about a variable.

## Future work
 
See the [issues page](https://github.com/sjcjoosten/amperspiegel/issues?utf8=%E2%9C%93&q=is%3Aopen). 
