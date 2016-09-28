# Run this in your terminal, make sure "demo" is your current directory
# Show that Ampersand scripts represent populations:

# clear
cat helloWorld1.ASL
amperspiegel -i helloWorld1.ASL
# Parse and show population
amperspiegel -i helloWorld1.ASL -show

# We can use amperspiegel to make a new parser
# With VIEW statements, we can define parsers
# clear
cat helloWorld2.ASL
amperspiegel -i helloWorld2.ASL -asParser
# now let's apply some rules to turn it into a parser:
amperspiegel -i helloWorld2.ASL -asParser -showP
# note that showP is just pretty syntax for a set of triples:
amperspiegel -i helloWorld2.ASL -asParser -show parser

# we can read in data in our own syntax:

# clear
cat fathers.txt
amperspiegel -i helloWorld2.ASL -asParser -i fathers.txt -show
# See how this was parsed how we defined it?
cat helloWorld2.ASL

# by the way, we did not recognise that Stef is the parent of Bas
# of course, we never specified this.
# Unfortunately, amperspiegel does not have a syntax to specify rules:
# clear
cat -n helloWorld3.ASL
amperspiegel -i helloWorld3.ASL

# Fortunately, we can create parsers in amperspiegel.
# Our default parser is called boot.ASL:

# open boot.ASL
# it's already rather large:
# clear
amperspiegel -i boot.ASL -count
amperspiegel -i boot.ASL -asParser -count
amperspiegel -i boot.ASL -asParser -count parser
# and we can even use it as a parser to parse our helloWorld2.ASL example:
# clear
amperspiegel -i boot.ASL -asParser -i helloWorld2.ASL -asParser -showP
amperspiegel -i helloWorld2.ASL -asParser -showP

# It's really the same parser! So we cannot parse rules with it (yet):
# clear
amperspiegel -i helloWorld3.ASL
amperspiegel -i boot.ASL -asParser -i helloWorld3.ASL

# I find it really exciting that I am getting the same error as last time.
# That's because it's really the same parser!

# So now let's edit boot.ASL, and add support for rules..
# (uncomment RULE stuff in boot.ASL)
# let's try again:
# clear
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
# So now let's use the full-fledged boot.ASL that has expressions defined:
amperspiegel -i ../base/boot.ASL -asParser -i helloWorld4.ASL -asParser -i fathers2.txt -show

