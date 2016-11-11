# Below, inline comments are printed as `# comment here`
echo "{-# OPTIONS_GHC -Wall -O0 #-} {-# LANGUAGE OverloadedStrings #-}" > BaseState.hs
echo "module BaseState (baseState) where{" >> BaseState.hs
echo "import Helpers;import TokenAwareParser;" >> BaseState.hs
echo "baseState :: [(Text,[Triple (Atom Text) (Atom Text)])];" >> BaseState.hs
echo "baseState =" >> BaseState.hs
echo -n "  [ " >> BaseState.hs
amperspiegel -i boot.ASL -asParser `# Use a parser that can parse asParser.ASL` \
             -i asParser.ASL `# add the parse-rules asParser.ASL` \
             -apply parser population asParser `# use it as parse rules` \
             -i cfg.ASL -apply asParser population cfg -parse test.cfg cfg cfg
             -apply del switches `# Remove switches` \
             -apply del population `# Remove population` \
             -collect state `# Collect the current state of amperspiegel` \
             -showTS state >> BaseState.hs
echo "  ];}" >> BaseState.hs
