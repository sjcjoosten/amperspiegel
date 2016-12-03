# amperspiegel -Parse xml.cfg cfg xml -Parse archi.cfg cfg archi -Parse Archisurance.xml xml -apply archi -show
amperspiegel -i ../base/boot.ASL -asParser `# Use a parser that can parse asParser.ASL` \
             -i ../base/asParser.ASL `# add the parse-rules asParser.ASL` \
             -apply parser population asParser `# use it as parse rules` \
             -i ../base/cfg.ASL -apply asParser population cfg `# setup cfg parser as when bootstrapped` \
             -Parse xml.cfg cfg xml -Parse archi.cfg cfg archi \
             -Parse Archisurance.xml xml -apply archi -show -print archi
             
