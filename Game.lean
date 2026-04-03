import Game.Levels.DemoWorld

-- Here's what we'll put on the title screen
Title "Math 323 Game"
Introduction
"
Welcome to the Math 323 Game! This game is meant to accompany the course
*Math 323: Formal Mathematical Reasoning and Writing* at the University of Arizona.

This game was developed by the UA Mathematics Lean Group under the leadership of
Sergey Cherkis and Rafa Munoz-Grenier.
"

Info "
Here you can put additional information about the game. It is accessible
from the starting through the drop-down menu.

For example: Game version, Credits, Link to Github and Zulip, etc.

Use **markdown**.
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
