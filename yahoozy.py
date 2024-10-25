#!/usr/bin/python3

import atexit
import bisect
import copy
import curses
import curses.panel
import curses.textpad
import getpass
import io
import itertools
import locale
import os
import random
import sys
from collections import UserDict
from dataclasses import dataclass
from enum import StrEnum
from pathlib import Path
from typing import Self, TextIO

if os.name == "posix":
	import termios

type Dice = tuple[int, int, int, int, int]
type LBEntry = tuple[int, str]


class Category(StrEnum):
	ONES      = "Ones"
	TWOS      = "Twos"
	THREES    = "Threes"
	FOURS     = "Fours"
	FIVES     = "Fives"
	SIXES     = "Sixes"
	ONE_PAIR  = "One Pair"
	TWO_PAIRS = "Two Pairs"
	TOAK      = "Three of a Kind"
	FOAK      = "Four of a Kind"
	SSTRAIGHT = "Small Straight"
	LSTRAIGHT = "Large Straight"
	FHOUSE    = "Full House"
	CHANCE    = "Chance"
	YATZY     = "Yatzy"

	def compute(self, dice: Dice) -> int:
		"""Return the points DICE will provide in the given category."""
		match self:
			case Category.ONES:
				return dice.count(1)
			case Category.TWOS:
				return dice.count(2) * 2
			case Category.THREES:
				return dice.count(3) * 3
			case Category.FOURS:
				return dice.count(4) * 4
			case Category.FIVES:
				return dice.count(5) * 5
			case Category.SIXES:
				return dice.count(6) * 6
			case Category.ONE_PAIR:
				g = (x for x in range(6, 0, -1) if dice.count(x) >= 2)
				try:
					return next(g) * 2
				except StopIteration:
					return 0
			case Category.TWO_PAIRS:
				g = (x for x in range(6, 0, -1) if dice.count(x) >= 2)
				try:
					return (next(g) + next(g)) * 2
				except StopIteration:
					return 0
			case Category.TOAK:
				g = (x for x in range(6, 0, -1) if dice.count(x) >= 3)
				try:
					return next(g) * 3
				except StopIteration:
					return 0
			case Category.FOAK:
				g = (x for x in range(6, 0, -1) if dice.count(x) >= 4)
				try:
					return next(g) * 4
				except StopIteration:
					return 0
			case Category.SSTRAIGHT:
				return 15 if set(dice) == {1, 2, 3, 4, 5} else 0
			case Category.LSTRAIGHT:
				return 20 if set(dice) == {2, 3, 4, 5, 6} else 0
			case Category.FHOUSE:
				g1 = (x for x in range(6, 0, -1) if dice.count(x) == 2)
				g2 = (x for x in range(6, 0, -1) if dice.count(x) == 3)
				try:
					next(g1)
					next(g2)
				except StopIteration:
					return 0
				return sum(dice)
			case Category.CHANCE:
				return sum(dice)
			case Category.YATZY:
				return 50 if len(set(dice)) == 1 else 0


class ScoreSheet(UserDict):
	def __lt__(self, other: Self) -> bool:
		return self.total() < other.total()

	def total(self) -> int:
		"""Return the current score."""
		lower = sum(self.get(c, 0) for c in LOWER_SECTION)
		upper = sum(self.get(c, 0) for c in UPPER_SECTION)
		bonus = 50 if upper >= 63 else 0
		return lower + upper + bonus


class Player:
	__slots__ = 'name', 'ss'

	def __init__(self, name: str) -> None:
		self.name = name
		self.ss = ScoreSheet()


class HelpPanel:
	def __init__(self, win, h: int, w: int, y: int, x: int) -> None:
		self._win = win.derwin(h, w, y, x)
		self._pan = curses.panel.new_panel(self._win)
		self._pan.top()
		self._opts: list[str] = []

		# Diagnostic message
		self.diag = ""

	def set_opts(self, *args: str) -> None:
		"""Set the list of available shortcuts.

		Shortcuts are strings where one of the characters is preceeded by
		an asterisk.  The character marked by the asterisk is the key
		that must be combined with the control key to execute the
		shortcut.
		"""
		self._opts = sorted(args, key=self._key)

	def draw(self) -> None:
		"""Draw the help panel.

		The help panel consists of two rows.  The top row is either empty
		or contains a diagnostic message intended for the user.  The
		bottom row shows the available keyboard shortcuts.

		Shortcuts are rendered as ‘^K DESCRIPTION’ where K is the marked
		key and DESCRIPTION is a relevant description.  As all shortcuts
		are mnemonic, the mnemonic letter is underlined for clarity.
		"""
		self._win.clear()
		if self.diag != "":
			self._win.addstr(self.diag, curses.A_DIM)
			self._win.addch(".", curses.A_DIM)
		self._win.move(1, 0)
		for i, opt in enumerate(self._opts):
			j = opt.find("*")
			ch = self._key(opt)
			if i != 0:
				self._win.addstr("    ")
			self._win.addstr(f"^{ch}  {opt[:j]}", curses.A_DIM)
			self._win.addch(ch, curses.A_DIM | curses.A_UNDERLINE)
			self._win.addstr(opt[j + 2:], curses.A_DIM)

	@staticmethod
	def _key(s: str) -> str:
		"""Extract the mnemonic key from S."""
		return s[s.find("*") + 1]


class NewPlayerPanel:
	def __init__(self, body_win) -> None:
		h, w = 7, 60
		bh, bw = body_win.getmaxyx()
		self.active = False
		self._win = body_win.subwin(
			h, w,
			bh // 2 - 4  + 3,
			bw // 2 - 30 + 1,
		)
		self._win.keypad(True)
		self._pan = curses.panel.new_panel(self._win)
		self._hp = HelpPanel(self._win, 2, w - 4, h - 3, 2)
		self._hp.set_opts("*Add Player", "*Exit Dialog")
		self._pan.top()
		self._pan.hide()
		self._hp.draw()

	def renaming(self) -> bool:
		"""Assert if we are renaming an existing player."""
		return self._pi >= 0

	def show(self, i: int) -> None:
		"""Display the new player panel, editing player at index I.

		If I is negative then add a new player instead of renaming an
		existing one.
		"""
		self.active = True
		self._bi = 0     # Button index
		self._pi = i     # Player index
		if i >= 0:
			self._text = players[-i - 1].name
			self._start_text = self._text
		else:
			self._text = ""
			self._start_text = None
		self._hp.diag = ""
		self._pan.show()

	def hide(self) -> None:
		"""Hide the new player panel."""
		self.active = False
		self._pan.hide()

	def draw(self) -> None:
		"""Draw the new player panel."""
		self._win.clear()
		self._hp.draw()

		self._win.addstr(
			5, 46, "[Add Player]",
			BTNSEL if self._bi == BTNAPP else BTNNSEL,
		)

		curses.textpad.rectangle(self._win, 1, 2, 3, 57)

		PLACEHOLDER = "Johnny Appleseed"
		self._win.addstr(2, 4, self._text)
		if self._text == "":
			self._win.addstr(2, 4, PLACEHOLDER, curses.A_DIM)
		self._win.addstr(
			2, 4 + (len(self._text) or len(PLACEHOLDER)), '█',
			curses.A_BOLD if self._bi == 0 else curses.A_DIM,
		)
		self._win.border()

	def handle_input(self) -> None:
		"""Handle user input in the new player panel.

		This method may hide the new player panel, or modify the global
		players array.
		"""
		k = self._win.get_wch()
		if k == "\x05":         # ^E
			self.hide()
		elif (
			k == "\x01"         # ^A
			or k == "\n" and self._bi == BTNAPP
		):
			if (pn := self._text.strip()) == "":
				self._hp.diag = "Empty player name not allowed"
			elif pn != self._start_text and any(p.name == pn for p in players):
				self._hp.diag = "Name already taken"
			else:
				if self.renaming():
					players[self._pi].name = pn
				else:
					players.append(Player(pn))
				self.hide()
		elif k == curses.KEY_UP:
			self._bi = 0
		elif k == curses.KEY_DOWN:
			self._bi = BTNAPP
		elif k == curses.KEY_BACKSPACE:
			self._text = self._text[:-1]
		elif type(k) == str and k.isprintable():
			self._text += k


@dataclass
class RenderState:
	sel: int       # The active/selected button
	togl: int      # A currently active/toggled option
	hp: HelpPanel


class DiceState:
	__slots__ = 'dice', 'rollmsk', 'rolls'

	def __init__(self) -> None:
		self.rolls = 2
		self.dice = [random.randint(1, 6) for _ in range(5)]

		# ROLLMSK is a 5-bit bitmask where each bit corresponds to a die
		# in DICE.  If a die’s corresponding bit is set, it means that
		# the user has selected the die for rerolling.
		self.rollmsk = 0

	def reroll_dice(self) -> None:
		"""Reroll the dice according to the reroll mask."""
		while self.rollmsk != 0:
			n = self.rollmsk.bit_length() - 1
			self.dice[n] = random.randint(1, 6)
			self.rollmsk ^= 1 << n
		self.rolls -= 1


TITLE = "Yahoozy — Yatzy not Yahtzee"

BTNNSEL = curses.A_BOLD                     # Button not selected
BTNSEL  = curses.A_BOLD | curses.A_STANDOUT # Button selected

BTNAP  = -1                     # ‘Add Player’ button
BTNSG  = -2                     # ‘Start Game’ button
BTNAPP = -3                     # ‘Add Player’ button (new player window)
BTNRP  = -4                     # ‘Remove Player’ button
BTNRR  = -5                     # ‘Reroll’ button
BTNKA  = -6                     # ‘Keep All’ button
BTNSC  = -7                     # ‘Select Category’ button

DICE_ART = [
	"     \n  •  \n     ",
	" •   \n     \n   • ",
	"   • \n  •  \n •   ",
	" • • \n     \n • • ",
	" • • \n  •  \n • • ",
	" • • \n • • \n • • ",
]

UPPER_SECTION = [
	Category.ONES,
	Category.TWOS,
	Category.THREES,
	Category.FOURS,
	Category.FIVES,
	Category.SIXES,
]

LOWER_SECTION = [
	c for c in Category
	if c not in UPPER_SECTION
]

# When the user first launches the game, there should by default already
# be one user registered with the name matching the current login name.
players: list[Player] = [Player(getpass.getuser().capitalize())]


def longest_length(*args: str) -> int:
	"""Return the length of the longest string in ARGS."""
	return max(map(len, args))

def draw_top10(body_win, hist: list[LBEntry]) -> None:
	"""Draw the all-time top 10 scores."""
	TOP_10_TITLE = "All-Time Top 10"

	# Compute the positions where we need to draw the leaderboard so that
	# it’s centered.
	y, x = body_win.getmaxyx()
	longest = longest_length(*hist, TOP_10_TITLE)
	yp, xp = y // 2 - 5, (x - longest) // 2

	body_win.addstr(yp, xp, TOP_10_TITLE, curses.A_BOLD)
	hist = ["%3d  %s" % x for x in hist]
	for i, x in enumerate(hist, 1):
		body_win.addstr(yp + i, xp, x)


def main(stdscr) -> None:
	# Create the history file if it doesn’t exist
	try:
		with histhandle("x") as _:
			pass
	except FileExistsError:
		pass

	with histhandle("r") as fp:
		hist = loadhist(fp, 10)

	curses.curs_set(0)
	curses.use_default_colors()

	# Draw the game title; this only ever needs to be drawn once.
	title_win = curses.newwin(3, curses.COLS - 2, 0, 1)
	title_attrs = curses.A_BLINK | curses.A_BOLD
	title_win.addstr(1, 3, "⚀ ⚀ ⚀ ⚀ ⚀", title_attrs)
	title_win.addstr(1, curses.COLS // 2 - len(TITLE) // 2, TITLE, title_attrs)
	title_win.addstr(1, curses.COLS - 14, "⚅ ⚅ ⚅ ⚅ ⚅", title_attrs)
	title_win.border()
	title_win.refresh()

	# Create a body window where we will proceed to draw all content for the
	# remainder of the program.
	body_height = curses.LINES - 3
	body_width = curses.COLS - 2
	body_win = curses.newwin(body_height, body_width, 3, 1)
	body_win.keypad(True)

	# Initialize panels
	h, w = body_win.getmaxyx()
	hp = HelpPanel(body_win, 2, w - 6, h - 3, 5)
	rs = RenderState(BTNAP, -1, hp)
	npp = NewPlayerPanel(body_win)

	while True:
		body_win.clear()

		# Draw player list
		body_win.addstr(2, 4, "Players", curses.A_BOLD)
		for i, p in enumerate(players):
			if not npp.active and len(players) - rs.sel - 1 == i:
				attr = BTNSEL
			else:
				attr = 0
			body_win.addstr(3 + i, 4, "[%s]" % p.name, attr)
		body_win.border()

		draw_top10(body_win, hist)

		rs.hp.set_opts("*Add Player", "*Quit Program", "*Start Game")
		rs.hp.draw()
		if npp.active:
			npp.draw()

		body_win.addstr(curses.LINES - 7, 5, "[Add Player]",
		                BTNNSEL if npp.active or rs.sel != BTNAP else BTNSEL)
		body_win.addstr(curses.LINES - 7, curses.COLS - 19, "[Start Game]",
		                BTNNSEL if npp.active or rs.sel != BTNSG else BTNSEL)

		body_win.refresh()

		if npp.active:
			npp.handle_input()
			continue

		k = body_win.get_wch()

		if k == "\x01":     # ^A
			npp.show(BTNAP)
		elif k == "\x11":   # ^Q
			sys.exit(0)

		# User tried to add/edit a player
		elif k == "\n" and (rs.sel == BTNAP or rs.sel >= 0):
			npp.show(rs.sel)

		# User tried to start the game
		elif (
			k == "\x13"     # ^S
			or k == "\n" and rs.sel == BTNSG
		):
			if len(players) == 0:
				rs.hp.diag = "Cannot start game with no players"
				continue

			game_loop(rs, body_win)

			# Once we reach here the user has finished the game.  We need
			# to reset the cursor to select the ‘Add Player’ button and
			# reload the history just in case the user broke into the
			# top-10.
			rs.sel = BTNAP
			with histhandle("r") as fp:
				hist = loadhist(fp, 10)

		elif k == curses.KEY_UP:
			if rs.sel < 0 and len(players) > 0:
				rs.sel = 0
			elif 0 <= rs.sel < len(players) - 1:
				rs.sel += 1
		elif k == curses.KEY_DOWN:
			if rs.sel > 0:
				rs.sel -= 1
			elif rs.sel == 0:
				rs.sel = BTNAP

		# Left and right between the two bottom-of-the-screen buttons
		elif k == curses.KEY_LEFT and rs.sel == BTNSG:
			rs.sel = BTNAP
		elif k == curses.KEY_RIGHT and rs.sel == BTNAP:
			rs.sel = BTNSG

		elif k == curses.KEY_BACKSPACE and rs.sel >= 0:
			players.pop(len(players) - rs.sel - 1)
			if len(players) == 0:
				rs.sel = BTNAP
			elif rs.sel != 0:
				rs.sel -= 1


def game_loop(rs: RenderState, body_win) -> None:
	"""The main game-loop."""
	ds = DiceState()
	playergen = itertools.cycle(players)
	player = next(playergen)

	rs.sel = BTNRR
	picking_cat = False

	longest_cat_name = max(map(len, Category))

	while True:
		body_win.clear()

		body_win.addstr(2, 4, "Current Player", curses.A_BOLD)
		body_win.addstr("   " + player.name)

		if not picking_cat:
			body_win.addstr(3, 4, "Rolls Remaining", curses.A_BOLD)
			body_win.addstr("  %d⁄3" % ds.rolls) # U+2044 FRACTION SLASH

		# Draw the leaderboard
		THDR = "Running Tally"
		rt = sorted(players, key=lambda x: x.ss, reverse=True)
		leaderboard = [f"{p.ss.total():3d}  {p.name}" for p in rt]
		longest = max(max(map(len, leaderboard)), len(THDR))

		_, x = body_win.getmaxyx()
		x_off = x - longest - 4
		body_win.addstr(2, x_off, THDR, curses.A_BOLD)
		for i, line in enumerate(leaderboard, 1):
			body_win.addstr(2 + i, x_off, line)

		# Draw the score sheet.  The following code is some absolute
		# black-magic stuff.  Straight out of Mordor.
		xtra = 10 if picking_cat else 0
		body_win.addstr(
			5, 4,
			"Score Sheet".center(longest_cat_name + 9 + xtra),
			curses.A_BOLD,
		)
		for i, category in enumerate(Category):
			s = player.ss.get(category, -1)
			body_win.move(7 + i, 5)

			if picking_cat:
				rowattrs = (
					BTNSEL if len(Category) - rs.sel - 1 == i
					else curses.A_BOLD if rs.togl == i
					else 0
				)

				if s == -1:
					body_win.addstr(checkbox(rs.togl == i), rowattrs)
				else:
					body_win.addstr("   ", rowattrs)
				body_win.addch(" ", rowattrs)
			else:
				rowattrs = 0

			body_win.addstr(category.ljust(longest_cat_name), rowattrs)

			if s == -1:
				body_win.addstr("     —", rowattrs)
				if picking_cat:
					arrow = "→"
					body_win.addstr(
						f" {arrow} {category.compute(ds.dice):2d}",
						rowattrs,
					)
			else:
				body_win.addstr(f"    {s:2d}", rowattrs)

		bar = "─" * (longest_cat_name + 6 + xtra)
		body_win.addstr(6,                 5, bar)
		body_win.addstr(len(Category) + 7, 5, bar)
		body_win.addstr(len(Category) + 8, 5, "Total".ljust(longest_cat_name))

		# Align the total with the category scores (which are now shifted
		# over because they’re surround in button indicators).
		if picking_cat:
			body_win.addstr("    ")

		total = player.ss.total()
		body_win.addstr(f"  {total:4d}")
		if picking_cat:
			sc = copy.deepcopy(player.ss)
			cat = list(Category)[rs.togl]
			sc[cat] = cat.compute(ds.dice)
			body_win.addstr(f" {arrow} {sc.total()}")
		curses.textpad.rectangle(
			body_win, 4, 3,
			9 + len(Category), 12 + longest_cat_name + xtra
		)

		dice_height = DICE_ART[0].count('\n') + 3
		dice_width = len(DICE_ART[0].split('\n')[0])
		bh, bw = body_win.getmaxyx()
		h, w = dice_height + 3, (dice_width + 8) * 5 + 2

		# We don’t need the reroll buttons anymore
		if picking_cat:
			h -= 1

		dice_win = body_win.subwin(
			h, w,
			bh - 12,
			bw // 2 - w // 2,
		)

		for i, d in enumerate(ds.dice):
			lines = DICE_ART[d - 1].split('\n')
			x_off = (dice_width + 8) * i + 3
			for j, line in enumerate(lines):
				dice_win.addstr(2 + j, x_off + 1, line)
			if not picking_cat:
				dice_win.addstr(
					dice_height + 1, x_off - 1,
					checkbox(ds.rollmsk & (1 << i)) + " Reroll",
					BTNSEL if rs.sel == i else BTNNSEL,
				)
			curses.textpad.rectangle(
				dice_win, 1, x_off,
				len(lines) + 2, x_off + dice_width + 1,
			)

		dice_win.box()
		dice_win.refresh()

		if picking_cat:
			body_win.addstr(curses.LINES - 7, bw - 22, "[Select Category]",
			                btnattrs(rs.sel == BTNSC))
		else:
			body_win.addstr(curses.LINES - 7, 5, "[Reroll]",
			                btnattrs(rs.sel == BTNRR))
			body_win.addstr(curses.LINES - 7, bw - 15, "[Keep All]",
			                btnattrs(rs.sel == BTNKA))

		opts = ["*Quit Program"]
		if picking_cat:
			opts.append("*Select Category")
		else:
			opts.extend([
				"Mark *All",
				"*Keep All",
				"*Reroll",
			])
		rs.hp.set_opts(*opts)
		rs.hp.draw()

		body_win.box()
		body_win.refresh()

		k = body_win.get_wch()
		if k == "\x11":         # ^Q
			sys.exit(0)

		if picking_cat:
			if (
				k == "\x13"     # ^S
				or k == "\n" and rs.sel == BTNSC
			):
				if rs.togl == -1:
					rs.hp.diag = "No category selected"
				else:
					cat = list(Category)[rs.togl]
					player.ss[cat] = cat.compute(ds.dice)
					ds = DiceState()
					player = next(playergen)
					picking_cat = False
					rs.hp.diag = ""
					rs.sel = BTNRR

					if player is players[0] and len(player.ss) == len(Category):
						rs.hp.diag = ""
						return game_end(rs, body_win)
			elif k == "\n" and rs.sel >= 0:
				rs.togl = len(Category) - rs.sel - 1

			elif k == curses.KEY_UP or k == curses.KEY_DOWN:
				can_select = [
					len(Category) - i - 1
					for i, cat in enumerate(Category)
					if cat not in player.ss
				]
				match k:
					case curses.KEY_UP if rs.sel == BTNSC:
						rs.sel = can_select[-1]
					case curses.KEY_UP:
						i = can_select.index(rs.sel)
						rs.sel = can_select[i - 1]
					case curses.KEY_DOWN if rs.sel == can_select[-1]:
						rs.sel = BTNSC
					case curses.KEY_DOWN if rs.sel != BTNSC:
						i = can_select.index(rs.sel)
						rs.sel = can_select[i + 1]

			elif k == curses.KEY_DOWN:
				if rs.sel > 0:
					rs.sel -= 1
				else:
					rs.sel = BTNSC
		else:
			if k == "\x01":     # ^A
				ds.rollmsk = 0b11111
			elif (
				k == "\x0B"     # ^K
				or k == "\n" and rs.sel == BTNKA
			):
				rs.sel = BTNSC
				rs.togl = -1
				rs.hp.diag = ""
				picking_cat = True
			elif (
				k == "\x12"     # ^R
				or k == "\n" and rs.sel == BTNRR
			):
				if ds.rolls == 0:
					rs.hp.diag = "No more rolls remaining"
				elif ds.rollmsk == 0:
					rs.hp.diag = "No dice selected to reroll"
				else:
					ds.reroll_dice()
			elif k == "\n" and rs.sel >= 0:
				ds.rollmsk ^= 1 << rs.sel
			elif k == curses.KEY_UP:
				if rs.sel == BTNRR:
					rs.sel = 0
				elif rs.sel == BTNKA:
					rs.sel = 4
			elif k == curses.KEY_DOWN and rs.sel >= 0:
				rs.sel = BTNRR
			elif k == curses.KEY_LEFT:
				if rs.sel == BTNKA:
					rs.sel = BTNRR
				elif rs.sel > 0:
					rs.sel -= 1
			elif k == curses.KEY_RIGHT:
				if rs.sel == BTNRR:
					rs.sel = BTNKA
				elif 0 <= rs.sel < 4:
					rs.sel += 1


def game_end(rs: RenderState, body_win) -> None:
	"""Display the end screen."""

	# Load the entire history file, add our scores to it (maintaining
	# order) and then write it back.
	with histhandle("r+") as fp:
		hist = loadhist(fp)
		for p in players:
			# Weird ‘bisect’ hack: it only lets us do sorted insertions
			# when we have an ascending sequence, so for our descending
			# sequence we negate the score in the key function.
			bisect.insort(hist, (p.ss.total(), p.name),
			              key=lambda x: (-x[0], x[1]))

		fp.seek(0, io.SEEK_SET)
		savehist(fp, hist)

	# Retain the first 10 entries for displaying
	hist = hist[:10]

	while True:
		body_win.clear()
		body_win.addstr(2, 4, "Game Over!", curses.A_BOLD)

		# Generate the leaderboard rows
		FINAL_TITLE = "Final Results"
		fr = sorted(players, key=lambda x: x.ss, reverse=True)
		leaderboard = [f"{p.ss.total():3d}  {p.name}" for p in fr]
		longest = longest_length(*leaderboard, FINAL_TITLE)

		# Draw the game leaderboard in the top-right
		y, x = body_win.getmaxyx()
		x_off = x - longest - 4
		body_win.addstr(2, x_off, FINAL_TITLE, curses.A_BOLD)
		for i, line in enumerate(leaderboard, 1):
			body_win.addstr(2 + i, x_off, line)

		draw_top10(body_win, hist)

		rs.hp.set_opts("*New Game", "*Quit Program")
		rs.hp.draw()

		body_win.box()
		body_win.refresh()

		k = body_win.get_wch()
		if k == "\x0E":         # ^N
			return
		elif k == "\x11":       # ^Q
			sys.exit(0)


def histhandle(mode: str) -> TextIO:
	"""Return a handle to the history file with MODE.
	
	If the history file doesn’t exist this function will create the
	necessary directories.  This function makes sure to abide by system-
	specific convensions.
	"""
	if os.name == "nt":
		assert (path := os.getenv("LOCALAPPDATA"))
		path = Path(path) / "Yahoozy"
	elif sys.platform == "darwin":
		assert (home := os.getenv("HOME"))
		path = (
			Path(home)
			/ "Library"
			/ "Application Support"
			/ "Yahoozy"
		)
	elif os.name == "posix":
		if (path := os.getenv("XDG_DATA_HOME")) == "":
			assert (path := os.getenv("HOME"))
			path = Path(path) / ".local" / "share" / "yahoozy"
		else:
			path = Path(path) / "yahoozy"
	else:
		raise NotImplementedError(f"No history support for {os.name}")

	path.mkdir(parents=True, exist_ok=True)
	return open(path / "history", mode)


def savehist(fp: TextIO, xs: list[LBEntry]) -> None:
	"""Save the history entries XS to the history file FP."""
	for x in xs:
		fp.write("%d\x1F%s\n" % x)    # 0x1F is the ASCII unit separator

def loadhist(fp: TextIO, n: int = -1) -> list[LBEntry]:
	"""Load the first N history entries from FP.
	
	If N is omitted this function returns all entries in FP.
	"""
	xs: list[LBEntry] = []
	for i in itertools.count():
		if i == n or (line := fp.readline()) == "":
			break
		score, name = line.rstrip("\n").split("\x1F")
		xs.append((int(score), name))
	return xs


def btnattrs(ckd: bool) -> int:
	"""Return the standard button attributes for an (un)checked button."""
	return BTNSEL if ckd else BTNNSEL

def checkbox(ckd: bool) -> str:
	"""Return a maybe checked checkbox."""
	return "[×]" if ckd else "[ ]"


def restore_term_settings(attrs: list) -> None:
	"""Restore terminal ATTRS on program exit."""
	fd = sys.stdin.fileno()
	termios.tcsetattr(fd, termios.TCSANOW, attrs)


if __name__ == "__main__":
	locale.setlocale(locale.LC_ALL, "")

	# Disable XON/XOFF on POSIX terminals to free up ^S and ^Q
	if os.name == "posix":
		fd = sys.stdin.fileno()
		old_attrs = termios.tcgetattr(fd)
		new_attrs = copy.deepcopy(old_attrs)
		# See the tcgetattr(3) description of ‘struct termios’ and
		# ‘c_iflag’ for more info
		new_attrs[0] &= ~(termios.IXANY | termios.IXOFF | termios.IXON)
		termios.tcsetattr(fd, termios.TCSANOW, new_attrs)
		# Restore terminal settings on exit
		atexit.register(restore_term_settings, old_attrs)

	curses.wrapper(main)
