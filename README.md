# AmbryTLA

TLA+ Specification for Ambry (https://github.com/linkedin/ambry)

## SETUP

### Using VSCode
- Install Visual Studio Code.
- Install the extensions "TLA+" and "TLA+ Nightly".
- Open the directory containing the tla+ and cfg files.
- Right-click, select "Check Model with TCL" and specify the below arguments
  `-deadlock -noTE -dump dot,actionlabels,colorize ATD -coverage 1`
  
### Using commandline
`java -cp tla2tools.jar tlc2.TLC -deadlock -noTE -dump dot,actionlabels,colorize AR -coverage 1 <filename>`
