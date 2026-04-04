import Game.Levels.S1_LeanAndLogic
import Game.Levels.S2_PredicateLogic
import Game.Levels.S3_Induction
import Game.Levels.S4_Sets
import Game.Levels.S5_Relations
import Game.Levels.S6_Functions
import Game.Levels.S7_Cardinality
import Game.Levels.S8_NumberSystems
import Game.Levels.S9_SupremumInfimum
import Game.Levels.S10_SequencesLimits
import Game.Levels.S11_Topology

-- Here's what we'll put on the title screen
Title "Math 323 Game"
Introduction
"
Welcome to Math 323 Game! This game is designed to accompany the course
*Math 323: Formal Mathematical Reasoning and Writing* at the University of Arizona.

This game was developed by
Jason Aubrey, Sergey Cherkis, and Rafa Munoz-Grenier.
"

Info "
Game version 0.1, University of Arizona Lean Group, https://github.com/cherkis/Math323Game.
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "Math323 Game"
CaptionLong "Game for Math323 course at the University of Arizona."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

Dependency LeanAndLogic → PredicateLogic → Induction
Dependency PredicateLogic → Sets
Dependency Sets → Relations → Functions → Cardinality
Dependency Sets → Functions
Dependency Induction → NumberSystems
Dependency Cardinality → NumberSystems → SupremumInfimum → SequencesLimits → Topology


/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
