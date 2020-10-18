#!/usr/bin/python3

# Copyright 2020 Mohamed El Morabity
#
# This program is free software: you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation, either version 3 of the License, or (at your option) any later
# version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
# details.
#
# You should have received a copy of the GNU General Public License along with
# this program. If not, see <http://www.gnu.org/licenses/>.

"""tv_grab_fr_telerama.py - Grab French television listings using the Télérama
mobile API in XMLTV format.
"""

from argparse import ArgumentParser
from argparse import Namespace
from concurrent.futures import ThreadPoolExecutor
from datetime import date
from datetime import time
from datetime import datetime
from datetime import timedelta
import hashlib
import hmac
import logging
import re
import sys
from pathlib import Path
from typing import Any
from typing import Dict
from typing import Generator
from typing import List
from typing import Optional
from typing import Set
from typing import Tuple
from typing import Union

from html2text import HTML2Text  # type: ignore
from lxml.etree import Element  # type: ignore # nosec
from lxml.etree import ElementTree  # nosec
import pytz
from pytz.reference import LocalTimezone  # type: ignore
from requests import Response
from requests import Session
from requests.exceptions import RequestException


class TeleramaException(Exception):
    """Base class for exceptions raised by the module."""


class Telerama:
    """Implements grabbing and processing functionalities required to generate
    XMLTV data from Télérama mobile API.
    """

    _API_URL = "https://api.telerama.fr"
    _API_USER_AGENT = "okhttp/3.12.3"
    _API_KEY = "apitel-g4aatlgif6qzf"
    _API_SECRET = "uIF59SZhfrfm5Gb"
    _API_DEVICE = "android_mobile"
    _API_DATE_FORMAT = "%Y-%m-%d"
    _API_TIME_FORMAT = "%H:%M"
    _API_DATETIME_FORMAT = f"{_API_DATE_FORMAT} %H:%M:%S"
    _API_TIMEZONE = pytz.timezone("Europe/Paris")

    _XMLTV_DATETIME_FORMAT = "%Y%m%d%H%M%S %z"

    _API_XMLTV_CREDITS = {
        "Acteur": "actor",
        "Auteur": "writer",
        "Autre Invité": "guest",
        "Autre présentateur": "presenter",
        "Compositeur": "composer",
        "Créateur": "writer",
        "Dialogue": "writer",
        "Guest star": "guest",
        "Interprète": "actor",
        "Invité vedette": "guest",
        "Invité": "guest",
        "Metteur en scène": "director",
        "Musique": "composer",
        "Origine Scénario": "presenter",
        "Présentateur vedette": "presenter",
        "Présentateur": "presenter",
        "Réalisateur": "director",
        "Scénario": "writer",
        "Scénariste": "writer",
        "Voix Off VF": "actor",
        "Voix Off VO": "actor",
    }

    _API_ETSI_CATEGORIES = {
        "Divertissement": "Show / Game show",
        "Documentaire": "News / Current affairs",
        "Film": "Movie / Drama",
        "Jeunesse": "Children's / Youth programmes",
        "Journal": "News / Current affairs",
        "Magazine": "Magazines / Reports / Documentary",
        "Musique": "Music / Ballet / Dance",
        "Sport": "Sports",
        "Série": "Movie / Drama",
        "Téléfilm": "Movie / Drama",
        "Téléréalité": "Show / Game show",
    }

    _RATING_ICON_URL_TEMPLATE = (
        "https://television.telerama.fr/sites/tr_master/themes/tr/html/images/"
        "tv/-{}.png"
    )

    # http://www.microsoft.com/typography/unicode/1252.htm
    _WINDOWS_1252_UTF_8 = {
        "\x80": "\u20AC",  # EURO SIGN
        "\x82": "\u201A",  # SINGLE LOW-9 QUOTATION MARK
        "\x83": "\u0192",  # LATIN SMALL LETTER F WITH HOOK
        "\x84": "\u201E",  # DOUBLE LOW-9 QUOTATION MARK
        "\x85": "\u2026",  # HORIZONTAL ELLIPSIS
        "\x86": "\u2020",  # DAGGER
        "\x87": "\u2021",  # DOUBLE DAGGER
        "\x88": "\u02C6",  # MODIFIER LETTER CIRCUMFLEX ACCENT
        "\x89": "\u2030",  # PER MILLE SIGN
        "\x8A": "\u0160",  # LATIN CAPITAL LETTER S WITH CARON
        "\x8B": "\u2039",  # SINGLE LEFT-POINTING ANGLE QUOTATION MARK
        "\x8C": "\u0152",  # LATIN CAPITAL LIGATURE OE
        "\x8E": "\u017D",  # LATIN CAPITAL LETTER Z WITH CARON
        "\x91": "\u2018",  # LEFT SINGLE QUOTATION MARK
        "\x92": "\u2019",  # RIGHT SINGLE QUOTATION MARK
        "\x93": "\u201C",  # LEFT DOUBLE QUOTATION MARK
        "\x94": "\u201D",  # RIGHT DOUBLE QUOTATION MARK
        "\x95": "\u2022",  # BULLET
        "\x96": "\u2013",  # EN DASH
        "\x97": "\u2014",  # EM DASH
        "\x98": "\u02DC",  # SMALL TILDE
        "\x99": "\u2122",  # TRADE MARK SIGN
        "\x9A": "\u0161",  # LATIN SMALL LETTER S WITH CARON
        "\x9B": "\u203A",  # SINGLE RIGHT-POINTING ANGLE QUOTATION MARK
        "\x9C": "\u0153",  # LATIN SMALL LIGATURE OE
        "\x9E": "\u017E",  # LATIN SMALL LETTER Z WITH CARON
        "\x9F": "\u0178",  # LATIN CAPITAL LETTER Y WITH DIAERESIS
    }

    def __init__(
        self,
        generator: Optional[str] = None,
        generator_url: Optional[str] = None,
    ):
        self._generator = generator
        self._generator_url = generator_url

        self._session = Session()
        self._session.headers.update({"User-Agent": self._API_USER_AGENT})
        self._session.hooks = {"response": [self._requests_raise_status]}

        initialization_data = self._query_api(
            "/v1/application/initialisation"
        ).get("donnees", {})
        self._genres = {
            genre_id: label
            for g in initialization_data.get("genres", [])
            if (genre_id := g.get("id")) and (label := g.get("libelle"))
        }
        self._channels = {
            self._telerama_to_xmltv_id(channel_id): {
                "id": channel_id,
                "display-name": name,
                "icon": {"src": c.get("logo")},
                "url": c.get("link"),
            }
            for c in initialization_data.get("chaines", [])
            if (channel_id := c.get("id")) and (name := c.get("nom"))
        }

    def __enter__(self):
        return self

    def __exit__(self, *args):
        if self._session:
            self._session.close()

    @staticmethod
    def _requests_raise_status(response: Response, *args, **kwargs) -> None:
        try:
            response.raise_for_status()
        except RequestException as ex:
            logging.debug(
                "Error while retrieving URL %s", response.request.url
            )
            try:
                raise TeleramaException(response.json().get("message") or ex)
            except ValueError:
                raise TeleramaException(ex)

    def _query_api(
        self, path: str, **query: Optional[Union[int, str]]
    ) -> Dict[str, Any]:
        # Authentication method taken from
        # https://github.com/zubrick/tv_grab_fr_telerama
        query["appareil"] = self._API_DEVICE

        signature = path + "".join(
            sorted([k + str(v) for k, v in query.items()])
        )
        query["api_signature"] = hmac.new(
            self._API_SECRET.encode(), signature.encode(), hashlib.sha1
        ).hexdigest()
        query["api_cle"] = self._API_KEY

        response = self._session.get(
            "{}/{}".format(self._API_URL, path.lstrip("/")), params=query,
        )

        logging.debug("Retrieved URL %s", response.request.url)

        return response.json()

    @classmethod
    def _telerama_to_xmltv_id(cls, channel_id: int) -> str:

        return f"{channel_id}.api.telerama.fr"

    def get_available_channels(self) -> Dict[str, str]:
        """Return the list of all available channels on Télérama, with their
        XMLTV ID and name.
        """

        return {k: v["display-name"] for k, v in self._channels.items()}

    @staticmethod
    def _datetime_ranges(
        start: datetime, days: int
    ) -> Generator[Tuple[datetime, datetime], None, None]:
        if start.hour != 23 or start.minute != 59:
            yield (start, start.replace(hour=23, minute=59))

        for day in range(1, days):
            yield (
                start.replace(hour=0, minute=0) + timedelta(days=day),
                start.replace(hour=23, minute=59) + timedelta(days=day),
            )

        if start.hour != 0 or start.minute != 0:
            yield (
                start.replace(hour=0, minute=0),
                start + timedelta(days=days),
            )

    def _get_program_ids(
        self, channel_ids: List[str], days: int, offset: int
    ) -> Generator[int, None, None]:
        start = datetime.combine(
            date.today(), time(0), tzinfo=LocalTimezone()
        ).astimezone(self._API_TIMEZONE) + timedelta(days=offset)

        telerama_channel_ids = [
            str(channel_id)
            for c in channel_ids
            if (channel_id := self._channels.get(c, {}).get("id"))
        ]

        seen = set()  # type: Set[int]
        for range_start, range_end in self._datetime_ranges(start, days):
            programs = self._query_api(
                "/v3/programmes/grille",
                date=range_start.strftime(self._API_DATE_FORMAT),
                heure_debut=range_start.strftime(self._API_TIME_FORMAT),
                heure_fin=range_end.strftime(self._API_TIME_FORMAT),
                id_chaines=",".join(telerama_channel_ids),
                page=1,
                nb_par_page=1000000,
            ).get("donnees", [])

            for program in programs:
                program_id = program.get("id_programme")
                if not program_id or program_id in seen:
                    continue
                seen.add(program_id)

                yield program_id

    @staticmethod
    def _xmltv_element(
        tag: str,
        text: Optional[str] = None,
        parent: Element = None,
        **attributes: Optional[str],
    ) -> Element:
        attributes = {k: v.strip() for k, v in attributes.items() if v}

        element = Element(tag, **attributes)
        if text:
            element.text = text

        if parent is not None:
            parent.append(element)

        return element

    @staticmethod
    def _xmltv_element_with_text(
        tag: str,
        text: Optional[str],
        parent: Element = None,
        **attributes: Optional[str],
    ) -> Optional[Element]:
        if text:
            text = text.strip()
        if not text:
            return None

        return Telerama._xmltv_element(
            tag, text=text, parent=parent, **attributes
        )

    def _to_xmltv_channel(self, channel_id: str) -> Optional[Element]:
        xmltv_channel = Element("channel", id=channel_id)

        channel_data = self._channels.get(channel_id)
        if not channel_data:
            return None

        # Channel display name
        self._xmltv_element_with_text(
            "display-name",
            channel_data.get("display-name"),
            parent=xmltv_channel,
        )

        # Icon associated to the programme
        self._xmltv_element(
            "icon", parent=xmltv_channel, **channel_data.get("icon", {})
        )

        # URL where you can find out more about the channel
        self._xmltv_element_with_text(
            "url", channel_data.get("url"), parent=xmltv_channel
        )

        return xmltv_channel

    @staticmethod
    def _get_xmltv_ns_episode_number(
        season: Optional[int],
        episode: Optional[int],
        total_episodes: Optional[int],
    ) -> Optional[str]:
        if not season and not episode:
            return None

        result = ""

        if season:
            result = f"{season - 1}"

        result += "."

        if episode:
            result += f"{episode - 1}"
            if total_episodes:
                result += f"/{total_episodes}"

        result += ".0/1"

        return result

    @classmethod
    def __to_fixed_utf8(cls, text: Optional[str]) -> str:
        if not text:
            return ""

        # Replace in a string all Windows-1252 specific chars to UTF-8 and
        # delete non XML-compatible characters
        fixed_text = "".join([cls._WINDOWS_1252_UTF_8.get(c, c) for c in text])
        fixed_text = re.sub(
            r"[\x00-\x08\x0b\x0E-\x1F\x7F\x90]", "", fixed_text
        )

        return fixed_text

    @staticmethod
    def _html_to_text(text: Optional[str]) -> str:
        if not text:
            return ""

        html_format = HTML2Text()
        html_format.ignore_emphasis = True
        html_format.body_width = False
        html_format.ignore_links = True
        return html_format.handle(text)

    # pylint: disable=too-many-branches
    # pylint: disable=too-many-locals
    # pylint: disable=too-many-statements
    def _to_xmltv_program(self, program: Dict[str, Any]) -> Optional[Element]:
        program_id = program.get("id_chaine")

        # Channel ID
        channel_id = self._telerama_to_xmltv_id(program.get("id_chaine", ""))
        if not channel_id:
            logging.debug("Program %s has no channel ID, skipping", program_id)
            return None

        # Start time
        try:
            start = self._API_TIMEZONE.localize(
                datetime.strptime(
                    program.get("horaire", {}).get("debut"),
                    self._API_DATETIME_FORMAT,
                )
            ).strftime(self._XMLTV_DATETIME_FORMAT)
        except ValueError:
            logging.debug(
                "Program %s has no valid start time, skipping", program_id,
            )
            return None

        # End time
        stop = None
        try:
            stop = self._API_TIMEZONE.localize(
                datetime.strptime(
                    program.get("horaire", {}).get("fin"),
                    self._API_DATETIME_FORMAT,
                )
            ).strftime(self._XMLTV_DATETIME_FORMAT)
        except ValueError:
            pass

        xmltv_program = self._xmltv_element(
            "programme",
            start=start,
            stop=stop,
            showview=program.get("showview"),
            channel=channel_id,
        )

        # Programme title
        title = program.get("titre") or program.get("soustitre")
        xmltv_title = self._xmltv_element_with_text(
            "title", title, parent=xmltv_program
        )
        if xmltv_title is None:
            logging.warning("Program %s has no title, skipping", program_id)
            return None

        if original_title := program.get("titre_original"):
            xmltv_title.set("lang", "fr")
            self._xmltv_element_with_text(
                "title", original_title, parent=xmltv_program,
            )

        # Sub-title or episode title
        if title != (sub_title := program.get("soustitre")):
            self._xmltv_element_with_text(
                "sub-title", sub_title, parent=xmltv_program
            )

        # Description of the programme or episode
        self._xmltv_element_with_text(
            "desc",
            self.__to_fixed_utf8(program.get("resume")),
            parent=xmltv_program,
        )

        # Credits for the programme
        xmltv_credits = self._xmltv_element("credits")
        _credits = {
            "director": {},
            "actor": {},
            "writer": {},
            "adapter": {},
            "producer": {},
            "composer": {},
            "editor": {},
            "presenter": {},
            "commentator": {},
            "guest": {},
        }  # type: Dict[str, Dict[str, Element]]
        for people in program.get("intervenants", []):
            label = people.get("libelle")
            credit = self._API_XMLTV_CREDITS.get(label)
            if not credit:
                if label:
                    logging.debug(
                        'No XMLTV credit defined for function "%s"', label,
                    )
                continue

            name = "{} {}".format(
                people.get("prenom", ""), people.get("nom", "")
            ).strip()
            if not name:
                continue

            _credits[credit][name] = self._xmltv_element_with_text(
                credit,
                name,
                role=people.get("role") if credit == "actor" else None,
            )

        xmltv_credits.extend(
            [e for s in _credits.values() for e in s.values()]
        )
        if len(xmltv_credits) > 0:
            xmltv_program.append(xmltv_credits)

        # Date the programme or film was finished
        self._xmltv_element_with_text(
            "date", program.get("annee_realisation"), parent=xmltv_program
        )

        # Type of programme
        genre = self._genres.get(program.get("id_genre"))
        self._xmltv_element_with_text(
            "category", genre, parent=xmltv_program, lang="fr"
        )
        self._xmltv_element_with_text(
            "category",
            program.get("genre_specifique"),
            parent=xmltv_program,
            lang="fr",
        )
        etsi_category = self._API_ETSI_CATEGORIES.get(genre or "")
        self._xmltv_element_with_text(
            "category", etsi_category, parent=xmltv_program, lang="en"
        )
        if genre and not etsi_category:
            logging.debug('No ETSI category found for genre "%s"', genre)

        # Icon associated to the programme
        icons = program.get("vignettes", {})
        if icon := (icons.get("grande") or icons.get("grande169")):
            self._xmltv_element(
                "icon", parent=xmltv_program, src=icon,
            )

        # URL where you can find out more about the programme
        self._xmltv_element_with_text(
            "url", program.get("url"), parent=xmltv_program,
        )

        # Country where the programme was made or one of the countries in a
        # joint production
        self._xmltv_element_with_text(
            "country",
            program.get("libelle_nationalite"),
            parent=xmltv_program,
            lang="fr",
        )

        # Episode number
        if series := program.get("serie", {}):
            self._xmltv_element_with_text(
                "episode-num",
                self._get_xmltv_ns_episode_number(
                    series.get("saison"),
                    series.get("numero_episode"),
                    series.get("nombre_episode"),
                ),
                parent=xmltv_program,
                system="xmltv_ns",
            )

        flags = program.get("flags", {})

        # Video details
        xmltv_video = self._xmltv_element("video", parent=xmltv_program)
        self._xmltv_element_with_text("present", "yes", parent=xmltv_video)

        aspect = None
        if flags.get("est_ar16x9"):
            aspect = "16:9"
        elif flags.get("est_ar4x3"):
            aspect = "4:3"
        self._xmltv_element_with_text("aspect", aspect, parent=xmltv_video)

        quality = None
        if flags.get("est_3d"):
            quality = "3DTV"
        elif flags.get("est_hd"):
            quality = "HDTV"
        self._xmltv_element_with_text("quality", quality, parent=xmltv_video)

        # Audio details
        xmltv_audio = self._xmltv_element("audio")

        stereo = None
        if flags.get("est_dolby"):
            stereo = "dolby"
        elif flags.get("est_stereoar16x9") or flags.get("est_stereo"):
            stereo = "stereo"
        elif flags.get("est_vm"):
            stereo = "bilingual"

        if stereo:
            xmltv_stereo = self._xmltv_element_with_text("stereo", stereo)
            self._xmltv_element_with_text("present", "yes", parent=xmltv_audio)
            xmltv_audio.append(xmltv_stereo)
            xmltv_program.append(xmltv_audio)

        # Previously shown programme?
        if flags.get("est_redif"):
            self._xmltv_element("previously-shown", parent=xmltv_program)
        # Premiere programme?
        elif (
            flags.get("est_premdif")
            or flags.get("est_inedit")
            or flags.get("est_inedit_crypte")
            or flags.get("est_nouveaute")
        ):
            self._xmltv_element("premiere", parent=xmltv_program)
        # Last chance to watch the programme?
        elif flags.get("est_derdif"):
            self._xmltv_element("last-chance", parent=xmltv_program)

        # Subtitles
        if flags.get("est_stm"):
            self._xmltv_element(
                "subtitles", parent=xmltv_program, type="deaf-signed"
            )
        if flags.get("est_vost"):
            self._xmltv_element(
                "subtitles", parent=xmltv_program, type="onscreen"
            )

        # Rating
        if rating := (program.get("csa_full") or [{}])[0]:
            if rating_value := rating.get("nom_long"):
                xmltv_rating = self._xmltv_element(
                    "rating", parent=xmltv_program
                )
                self._xmltv_element_with_text(
                    "value", rating_value, parent=xmltv_rating
                )
                try:
                    self._xmltv_element(
                        "icon",
                        parent=xmltv_rating,
                        src=self._RATING_ICON_URL_TEMPLATE.format(
                            int(rating.get("nom_court"))
                        ),
                    )
                except ValueError:
                    pass

        # Star rating
        if star_rating := program.get("note_telerama"):
            xmltv_star_rating = self._xmltv_element(
                "star-rating", parent=xmltv_program
            )
            self._xmltv_element_with_text(
                "value", f"{star_rating}/5", parent=xmltv_star_rating,
            )

        # Review
        review = self._html_to_text(program.get("critique"))
        notes = self._html_to_text(program.get("notule"))
        self._xmltv_element_with_text(
            "review",
            self.__to_fixed_utf8(f"{review}\n\n{notes}".strip(" \n\u200b")),
            parent=xmltv_program,
            type="text",
            lang="fr",
        )

        return xmltv_program

    def _get_xmltv_programs(
        self, channel_ids: List[str], days: int, offset: int
    ) -> Generator[Element, None, None]:

        with ThreadPoolExecutor() as executor:
            futures = [
                executor.submit(self._query_api, f"/v1/programmes/{p}")
                for p in self._get_program_ids(channel_ids, days, offset)
            ]

            for future in futures:
                program = None

                try:
                    program = future.result().get("donnees")
                except TeleramaException as ex:
                    logging.debug(ex)

                if not program:
                    continue

                yield self._to_xmltv_program(program[0])

    def _to_xmltv(
        self, channel_ids: List[str], days: int, offset: int
    ) -> ElementTree:
        xmltv = self._xmltv_element(
            "tv",
            **{
                "source-info-name": "Télérama",
                "source-info-url": "http://www.telerama.fr/",
                "source-data-url": self._API_URL,
                "generator-info-name": self._generator,
                "generator-info-url": self._generator_url,
            },
        )

        xmltv_channels = {}  # type: Dict[str, Element]
        xmltv_programs = []
        for xmltv_program in self._get_xmltv_programs(
            channel_ids, days, offset
        ):
            if xmltv_program is None:
                continue
            channel_id = xmltv_program.get("channel")
            if channel_id not in xmltv_channels:
                xmltv_channels[channel_id] = self._to_xmltv_channel(channel_id)
            xmltv_programs.append(xmltv_program)

        xmltv.extend(xmltv_channels.values())
        xmltv.extend(xmltv_programs)

        return ElementTree(xmltv)

    def write_xmltv(
        self, channel_ids: List[str], output_file: Path, days: int, offset: int
    ) -> None:
        """Grab Télérama programs in XMLTV format and write them to file."""

        logging.debug("Writing XMLTV program to file %s", output_file)

        xmltv_data = self._to_xmltv(channel_ids, days, offset)
        xmltv_data.write(
            str(output_file),
            encoding="UTF-8",
            xml_declaration=True,
            pretty_print=True,
        )


_PROGRAM = "tv_grab_fr_telerama"
__version__ = "2.2"
__url__ = "https://github.com/melmorabity/tv_grab_fr_telerama"

_DESCRIPTION = "France (Télérama)"
_CAPABILITIES = ["baseline", "manualconfig"]

_DEFAULT_DAYS = 1
_DEFAULT_OFFSET = 0

_DEFAULT_CONFIG_FILE = Path.home().joinpath(".xmltv", f"{_PROGRAM}.conf")


def _print_description() -> None:
    print(_DESCRIPTION)


def _print_version() -> None:
    print("This is {} version {}".format(_PROGRAM, __version__))


def _print_capabilities() -> None:
    print("\n".join(_CAPABILITIES))


def _parse_cli_args() -> Namespace:
    parser = ArgumentParser(
        description="get French television listings using Télérama mobile "
        "API in XMLTV format"
    )
    parser.add_argument(
        "--description",
        action="store_true",
        help="print the description for this grabber",
    )
    parser.add_argument(
        "--version",
        action="store_true",
        help="show the version of this grabber",
    )
    parser.add_argument(
        "--capabilities",
        action="store_true",
        help="show the capabilities this grabber supports",
    )
    parser.add_argument(
        "--configure",
        action="store_true",
        help="generate the configuration file by asking the users which "
        "channels to grab",
    )
    parser.add_argument(
        "--days",
        type=int,
        default=_DEFAULT_DAYS,
        help="grab DAYS days of TV data (default: %(default)s)",
    )
    parser.add_argument(
        "--offset",
        type=int,
        default=_DEFAULT_OFFSET,
        help="grab TV data starting at OFFSET days in the future (default: "
        "%(default)s)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("/dev/stdout"),
        help="write the XML data to OUTPUT instead of the standard output",
    )
    parser.add_argument(
        "--config-file",
        type=Path,
        default=_DEFAULT_CONFIG_FILE,
        help="file name to write/load the configuration to/from (default: "
        "%(default)s)",
    )

    log_level_group = parser.add_mutually_exclusive_group()
    log_level_group.add_argument(
        "--quiet",
        action="store_true",
        help="only print error-messages on STDERR",
    )
    log_level_group.add_argument(
        "--debug",
        action="store_true",
        help="provide more information on progress to stderr to help in"
        "debugging",
    )

    return parser.parse_args()


def _read_configuration(
    available_channels: Dict[str, str], config_file: Path
) -> List[str]:

    channel_ids = set()
    with config_file.open("r") as config_reader:
        for line in config_reader:
            match = re.search(r"^\s*channel\s*=\s*(.+)\s*(#.*)?", line)
            if match is None:
                continue

            channel_id = match.group(1)
            if channel_id in available_channels:
                channel_ids.add(channel_id)

    return list(channel_ids)


def _write_configuration(channel_ids: List[str], config_file: Path) -> None:

    config_file.parent.mkdir(parents=True, exist_ok=True)

    with open(config_file, "w") as config:
        for channel_id in channel_ids:
            print("channel={}".format(channel_id), file=config)


def _configure(available_channels: Dict[str, str], config_file: Path) -> None:
    channel_ids = []
    answers = ["yes", "no", "all", "none"]
    select_all = False
    select_none = False
    print(
        "Select the channels that you want to receive data for.",
        file=sys.stderr,
    )
    for channel_id, channel_name in available_channels.items():
        if not select_all and not select_none:
            while True:
                prompt = f"{channel_name} [{answers} (default=no)] "
                answer = input(prompt).strip()  # nosec
                if answer in answers or answer == "":
                    break
                print(
                    f"invalid response, please choose one of {answers}",
                    file=sys.stderr,
                )
            select_all = answer == "all"
            select_none = answer == "none"
        if select_all or answer == "yes":
            channel_ids.append(channel_id)
        if select_all:
            print(f"{channel_name} yes", file=sys.stderr)
        elif select_none:
            print(f"{channel_name} no", file=sys.stderr)

    _write_configuration(channel_ids, config_file)


def _main() -> None:
    args = _parse_cli_args()

    if args.version:
        _print_version()
        sys.exit()

    if args.description:
        _print_description()
        sys.exit()

    if args.capabilities:
        _print_capabilities()
        sys.exit()

    logging_level = logging.INFO
    if args.quiet:
        logging_level = logging.ERROR
    elif args.debug:
        logging_level = logging.DEBUG
    logging.basicConfig(
        level=logging_level, format="%(levelname)s: %(message)s",
    )

    telerama = Telerama(generator=_PROGRAM, generator_url=__url__)

    logging.info("Using configuration file %s", args.config_file)

    available_channels = telerama.get_available_channels()
    if args.configure:
        _configure(available_channels, args.config_file)
        sys.exit()

    if not args.config_file.is_file():
        logging.error(
            "You need to configure the grabber by running it with --configure"
        )
        sys.exit(1)

    channel_ids = _read_configuration(available_channels, args.config_file)
    if not channel_ids:
        logging.error(
            "Configuration file %s is empty or malformed, delete and run with "
            "--configure",
            args.config_file,
        )
        sys.exit(1)

    try:
        telerama.write_xmltv(
            channel_ids, args.output, days=args.days, offset=args.offset
        )
    except TeleramaException as ex:
        logging.error(ex)


if __name__ == "__main__":
    _main()
