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
             -i cfg.ASL -apply asParser population cfg \
             -Parse rules.cfg cfg rules -Parse basic.cfg cfg cfg2 -parse basic.cfg cfg2 cfg2 -apply rules cfg2 cfg2 `# cfg2 as basic grammar` \
             -apply del switches `# Remove switches` \
             -apply del population `# Remove population` \
             -collect state `# Collect the current state of amperspiegel` \
             -showTS state >> BaseState.hs
echo "  ];}" >> BaseState.hs
