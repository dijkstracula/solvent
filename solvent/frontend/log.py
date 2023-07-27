import logging
import sys
from pathlib import Path

from ansi.color import fg, fx


class CustomFormatter(logging.Formatter):
    FORMATS = {
        logging.DEBUG: fg.green,
        logging.INFO: fg.blue,
        logging.WARNING: fg.yellow,
        logging.ERROR: fg.red,
        logging.CRITICAL: fg.boldred,
    }

    def format(self, record):
        args = record.args
        record.args = None
        raw_msg: str = record.getMessage()

        if args is not None and len(args) != 0:
            use_multiline = True
            title = raw_msg
            fmtted_msg = "\n".join(map(str, args))
            record.args = None
        else:
            use_multiline = "\n" in raw_msg
            title = ""
            fmtted_msg = raw_msg

        if use_multiline:
            bar = f"\n{fg.darkgray}│{fx.reset} "
            msg = (
                title
                + bar
                + fmtted_msg.replace("\n", bar)
                + f"\n{fg.darkgray}└─────{fx.reset}"
            )
            beg = f"{fg.darkgray}┌{fx.reset}"
        else:
            beg = f"{fg.darkgray}•{fx.reset}"
            msg = fmtted_msg

        raw_filename = Path(record.pathname)
        last_idx = max(
            loc for loc, val in enumerate(raw_filename.parts) if val == "solvent"
        )
        filename = "/".join(raw_filename.parts[last_idx + 1 :])
        return (
            f"{beg}{self.FORMATS[record.levelno]}{record.levelname}{fx.reset}"
            + " "
            + f"{fg.darkgray}{fx.italic}{fx.faint}{filename}"
            + ":"
            + f"{record.lineno}{fx.reset}"
            + " "
            + msg
        )


def install(debug=False):
    root_logger = logging.getLogger()
    if debug:
        root_logger.setLevel(logging.DEBUG)
    else:
        root_logger.setLevel(logging.WARNING)
    console_handler = logging.StreamHandler(stream=sys.stdout)
    colored_formatter = CustomFormatter()
    console_handler.setFormatter(colored_formatter)
    root_logger.addHandler(console_handler)
