"""
Drive squirreltop with Python! TODO !
=========================

This module is a simple pexpect-based driver for squirreltop, based on the old
REPL interface.
"""

import os
import re

import pexpect


class SquirrelTopError(Exception):
    def __init__(self, err, last_sentence, before):
        super().__init__()
        self.err = err
        self.before = before
        self.last_sentence = last_sentence

class SquirrelTop:
    """Create an instance of squirreltop.

    Use this as a context manager: no instance of squirreltop is created until
    you call `__enter__`.  squirreltop is terminated when you `__exit__` the
    context manager.

    Sentence parsing is very basic for now (a "." in a quoted string will
    confuse it).
    """

    # COQTOP_PROMPT = re.compile("\r\n[^< \r\n]+ < ")
    SQUIRRELTOP_PROMPT = re.compile("\[> ")

    def __init__(self, squirreltop_bin=None, color=False, args=None) -> str:
        """Configure a squirreltop instance (but don't start it yet).

        :param squirreltop_bin: The path to squirreltop; uses $SQUIRRElBIN by default, falling back to "squirreltop"
        :param color:      When True, tell squirreltop to produce ANSI color codes (see
                           the ansicolors module)
        :param args:       Additional arguments to squirreltop.
        """
        self.squirreltop_bin = squirreltop_bin or os.path.join(os.getenv('SQUIRRELBIN', ""), "squirrel")
        if not pexpect.utils.which(self.squirreltop_bin):
            print(f"squirreltop binary not found: "+format(self.squirreltop_bin))
            raise ValueError("squirreltop binary not found: '{}'".format(self.squirreltop_bin))
        self.args = (args or []) + ["-i"]
        self.squirreltop = None

    def __enter__(self):
        if self.squirreltop:
            raise ValueError("This module isn't re-entrant")
        # TODO ↓
        self.squirreltop = pexpect.spawn(self.squirreltop_bin, args=self.args, echo=False, encoding="utf-8")
        # Disable delays (http://pexpect.readthedocs.io/en/stable/commonissues.html?highlight=delaybeforesend)
        self.squirreltop.delaybeforesend = 0
        self.next_prompt()
        return self

    def __exit__(self, type, value, traceback):
        print("Exiting squirreltop")
        self.squirreltop.kill(9)

    def next_prompt(self):
        """Wait for the next squirreltop prompt, and return the output preceding it."""
        print("Wait squirreltop")
        self.squirreltop.expect(SquirrelTop.SQUIRRELTOP_PROMPT, timeout = 10)
        return self.squirreltop.before

    def sendone(self, sentence):
        """Send a single sentence to squirreltop.

        :sentence: One Squirrel sentence (otherwise, squirreltop will produce multiple
                   prompts and we'll get confused)
        """
        # Suppress newlines, but not spaces: they are significant in notations
        sentence = re.sub(r"[\r\n]+", " ", sentence).strip()
        try:
            self.squirreltop.sendline(sentence)
            output = self.next_prompt()
        except Exception as err:
            raise SquirrelTopError(err, sentence, self.squirreltop.before)
        return output.strip()

    def send_initial_options(self):
        """Options to send when starting the toplevel and after a Reset Initial."""
        # self.sendone('include Basic.')

def sendmany(*sentences):
    """A small demo: send each sentence in sentences and print the output"""
    with SquirrelTop() as squirreltop:
        for sentence in sentences:
            print("=====================================")
            print(sentence)
            print("-------------------------------------")
            response = squirreltop.sendone(sentence)
            print(response)

def main():
    """Run a simple performance test and demo `sendmany`"""
    with SquirrelTop() as squirreltop:
        for _ in range(200):
            print(repr(squirreltop.sendone("Check nat.")))
        sendmany("lemma _ : False.", "Proof.", "admit", "Qed.")

if __name__ == '__main__':
    main()
