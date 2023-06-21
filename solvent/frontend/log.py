import logging
import sys

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
        raw_msg = record.getMessage()
        if "\n" in raw_msg:
            bar = f"\n{fg.darkgray}│{fx.reset} "
            msg = bar + raw_msg.replace("\n", bar) + f"\n{fg.darkgray}└──────{fx.reset}"
            beg = f"{fg.darkgray}┌{fx.reset}"
        else:
            beg = f"{fg.darkgray}•{fx.reset}"
            msg = raw_msg

        return "".join(
            [
                f"{beg}{self.FORMATS[record.levelno]}{record.levelname}{fx.reset}",
                " ",
                f"{fg.gray}{fx.italic}{fx.faint}{record.filename}",
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
        root_logger.setLevel(logging.INFO)
    console_handler = logging.StreamHandler(stream=sys.stdout)
    colored_formatter = CustomFormatter()
    console_handler.setFormatter(colored_formatter)
    root_logger.addHandler(console_handler)
