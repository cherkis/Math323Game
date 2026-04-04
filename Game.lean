import Game.Levels.S1.L01
import Game.Levels.S2.L03

-- Here's what we'll put on the title screen
Title "Math 323 Game"
Introduction
"
Welcome to Math 323 Game! This game is designed to accompany the course
*Math 323: Formal Mathematical Reasoning and Writing* at the University of Arizona.

This game was developed by the UA Mathematics Lean Group under the leadership of
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

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
