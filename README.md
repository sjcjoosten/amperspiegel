#
# INSTALLATION
# 

The software is tested with GHC-8.0.1
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

```
cd demo
# Show that Ampersand scripts represent populations:

clear
cat helloWorld1.ASL
amperspiegel -i helloWorld1.ASL
# Parse and show population
amperspiegel -i helloWorld1.ASL -show

# We can use amperspiegel to make a new parser
# With VIEW statements, we can define parsers
clear
cat helloWorld2.ASL
amperspiegel -i helloWorld2.ASL -asParser
# now let's apply some rules to turn it into a parser:
amperspiegel -i helloWorld2.ASL -asParser -showP
# note that showP is just pretty syntax for a set of triples:
amperspiegel -i helloWorld2.ASL -asParser -show parser

# we can read in data in our own syntax:

clear
cat fathers.txt
amperspiegel -i helloWorld2.ASL -asParser -i fathers.txt -show
# See how this was parsed how we defined it?
cat helloWorld2.ASL

# by the way, we did not recognise that Stef is the parent of Bas
# of course, we never specified this.
# Unfortunately, amperspiegel does not have a syntax to specify rules:
clear
cat -n helloWorld3.ASL
amperspiegel -i helloWorld3.ASL

# Fortunately, we can create parsers in amperspiegel.
# Our default parser is called boot.ASL:

open boot.ASL
# it's already rather large:
clear
amperspiegel -i boot.ASL -count
amperspiegel -i boot.ASL -asParser -count
amperspiegel -i boot.ASL -asParser -count parser
# and we can even use it as a parser to parse our helloWorld2.ASL example:
clear
amperspiegel -i boot.ASL -asParser -i helloWorld2.ASL -asParser -showP
amperspiegel -i helloWorld2.ASL -asParser -showP

# It's really the same parser! So we cannot parse rules with it (yet):
clear
amperspiegel -i helloWorld3.ASL
amperspiegel -i boot.ASL -asParser -i helloWorld3.ASL

# I find it really exciting that I am getting the same error as last time.
# That's because it's really the same parser!

# So now let's edit boot.ASL, and add support for rules..
# (uncomment RULE stuff in boot.ASL)
# let's try again:
clear
amperspiegel -i boot.ASL -asParser -i helloWorld3.ASL

# Succes!
# Now let's see how our example goes
cat fathers.txt
amperspiegel -i boot.ASL -asParser -i helloWorld3.ASL -asParser -i fathers.txt -show

# Let's pick it up a notch
cat fathers2.txt
amperspiegel -i boot.ASL -asParser -i helloWorld3.ASL -asParser -i fathers2.txt
# That won't do, Man Bas is the same guy here...
cat helloWorld4.ASL
# So now let's use a boot.ASL that has expressions defined:
amperspiegel -i boot2.ASL -asParser -i helloWorld4.ASL -asParser -i fathers2.txt -show
```

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
 
See the [issues page](https://github.com/sjcjoosten/amperspiegel/issues?utf8=%E2%9C%93&q=is%3Aopen%20label%3A%22Must%20have%22%20label%3A%22Want%20to%20have%22%20). 
