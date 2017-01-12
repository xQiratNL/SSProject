# SSProject
* Delimiter: “;”
* Port number: “1337”
* 0,0,0 is the back, left corner
* TimeOut = USERQUIT (20 seconds)

##Client

###Connect to server
* `HELLO <Username> [Chat] [Leaderboard] [Challenge]`

###Start a game
* `1a. 			PLAY HUMAN <Number of players> [Dimension]`
* `1b. 	PLAY COMPUTER <Number of players> [Dimension]`
* `
* `3a.		READY`
* `3b.		DECLINE`

###Playing a game
* `1. 		MAKEMOVE <x> <y> <z>`

###Chat
* `		BROADCAST <text>`
* `		WHISPER <username> <text>`
* `		CHATUSERS`
* `		GAMECHAT <text>`

###Challenge
* `		CHALLENGE <Username> [Username 1] … [Username n]`
* `		ACCEPT`
* `		CHALLENGEDECLINE`
* `		STATUS <Username>`
* `		AVAILABLE`

###Leaderboard
* `		LEADERBOARD`

###Password	
*		`PASSWORD <hash of password>`

##Server

###Connect to server
* `2a. 		HELLO [Chat] [Leaderboard] [Challenge]`
* `2b. 		ERR_USERNAME\_TAKEN`

###Start a game
* `2a.		WAIT`
* `2b.		READY <Username1> <Username2> [Username 3] … [Username n]`
* in case of DECLINE, go to 2a

###Playing a game
* `1. 		REQUESTMOVE <Username>`
* `2a. 		SETMOVE <Username> <x> <y> <z>`
* `2b. 		ERR_INVALIDMOVE <x> <y> <z>`
* `2c.		ERR_NOTYOURTURN`
* `3a.		GAMEOVER [Username of winner]`
* `3b.		ERR_USERQUIT <Username of quitter>`

###Chat
* `		BROADCAST <Username who did sent the message> <text> `(voor iedereen op de server)
* `		WHISPER <Username who did sent the message> <text>` (voor 1 user)
* `		CHATUSERS <Username (of the one who requested it)> [Username 1] … [Username n]`
* `		GAMECHAT <user> <text> `(voor iedereen in de game)
* `		ERR_USERNOTFOUNDCHAT`
* `		ERR_USERHASNOCHAT`
* `		ERR_NOTINAGAME`

###Challenge
* `		CHALLENGED <Username> [Username 1] … [Username n]`
* `		CANCELLED <USERNAME>`
* `		ERR_USERNOTFOUNDCHALLENGE <Username> [Username 1] … [Username n]`
* `		ERR_USERINGAME <Username> [Username 1] … [Username n]`
* `		ERR_USERHASNOCHALLENGE <Username> [Username 1] … [Username n]`
* `		STATUS <Username> AVAILABLE/NOT`
* `		AVAILABLE [Username 1] … [Username n]`

###Leaderboard
*	`	LEADERBOARD <Username> <points> `(send this command multiple times)

###Password
* `		REQUESTPASSWORD`
* `		ACCESSGRANTED`
* `		ERR_ACCESSDENIED`
* `		REGISTERED		`
* if username is not taken, it automatically creates an account when you sent a password. You get both the Access granted & the registered message

###Other
*	`	ERR_COMMANDNOTRECOGNIZED <Command>`