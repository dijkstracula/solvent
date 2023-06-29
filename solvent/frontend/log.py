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
        if record.args is not None:
            # if we have args, join them with a space
            args = "\n".join(map(str, record.args))
            # we are handling args ourselves, so we set
            # record.args to None so that it doesn't yell at us
            record.args = None
            raw_msg = f"{record.getMessage()} {args}"
        else:
            raw_msg = f"{record.getMessage()}"

        if "\n" in raw_msg:
            bar = f"\n{fg.darkgray}│{fx.reset} "
            msg = bar + raw_msg.replace("\n", bar) + f"\n{fg.darkgray}└─────{fx.reset}"
            beg = f"{fg.darkgray}┌{fx.reset}"
        else:
            beg = f"{fg.darkgray}•{fx.reset}"
            msg = raw_msg

        raw_filename = Path(record.pathname)
        last_idx = max(
            loc for loc, val in enumerate(raw_filename.parts) if val == "solvent"
        )
        filename = "/".join(raw_filename.parts[last_idx + 1 :])
        return "".join(
            [
                f"{beg}{self.FORMATS[record.levelno]}{record.levelname}{fx.reset}",
                " ",
                f"{fg.darkgray}{fx.italic}{fx.faint}{filename}",
                ":",
                f"{record.lineno}{fx.reset}",
                " ",
                msg,
            ]
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
