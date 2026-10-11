#!/usr/bin/env python3
# WFC Circuit Studio — PCB/logic generator + EDA analysis + MCTS + footprints
#                   + custom JSON tilesets + stub autorouter + minimap/zoom
#                   + solve timeline/GIF + zone painting
# Requires: pip install PySide6   (optional: Pillow for GIF export)

import heapq
import io
import json
import math
import random
import sys
import time
from collections import defaultdict, deque
from dataclasses import dataclass
from itertools import count

from PySide6.QtCore import Qt, QBuffer, QEvent, QTimer, QPointF, QRectF, QSize, QRect
from PySide6.QtGui import (QColor, QFont, QImage, QKeySequence, QPainter,
                           QPainterPath, QPixmap, QPen, QShortcut)
from PySide6.QtWidgets import (QAbstractItemView, QApplication, QCheckBox,
                               QComboBox, QDockWidget, QDoubleSpinBox,
                               QFileDialog, QGridLayout, QGroupBox, QHBoxLayout,
                               QLabel, QListWidget, QListWidgetItem, QMainWindow,
                               QPushButton, QScrollArea, QSlider, QSpinBox,
                               QSplitter, QTabWidget, QTableWidget,
                               QTableWidgetItem, QVBoxLayout, QWidget)

try:
    from PySide6.QtSvg import QSvgGenerator
    HAS_SVG = True
except Exception:
    HAS_SVG = False

N, E, S, W = range(4)
DIRS = ((0, -1), (1, 0), (0, 1), (-1, 0))
DIRL = "NESW"
OPP = (2, 3, 0, 1)
OUTV = (QPointF(0, -1), QPointF(1, 0), QPointF(0, 1), QPointF(-1, 0))
MAX_ATTEMPTS = 50
INNER_BASE = 40          # socket ids >= this are footprint-internal seams


# --------------------------------------------------------------------------- tiles

@dataclass
class Tile:
    base: str
    edges: tuple
    base_edges: tuple
    kind: str
    weight: float = 1.0
    rot: int = 0


@dataclass
class Theme:
    bg: QColor
    cell: QColor
    grid: QColor
    sockets: dict
    via: QColor
    pad: QColor
    gate_fill: QColor
    gate_edge: QColor
    glow: bool = False
    bus_socket: int = 0


@dataclass
class TilesetDef:
    name: str
    flavor: str            # "pcb" | "logic" — analysis/export behaviour
    theme: Theme
    socket_names: dict
    bus_socket: int
    singles: list          # (base, edges, kind, sym)
    fps: list              # footprint spec dicts
    weights: dict          # base -> default weight


PCB_THEME = Theme(
    bg=QColor("#0a2718"), cell=QColor("#0e3220"), grid=QColor(255, 255, 255, 14),
    sockets={1: QColor("#e3b23c"), 2: QColor("#e2503c"), 3: QColor("#4f8fdd")},
    via=QColor("#e3b23c"), pad=QColor("#cdd5da"),
    gate_fill=QColor("#161c24"), gate_edge=QColor("#dfe7ee"), bus_socket=0,
)
LOGIC_THEME = Theme(
    bg=QColor("#0d1117"), cell=QColor("#141b22"), grid=QColor(255, 255, 255, 12),
    sockets={1: QColor("#3ecf70"), 2: QColor("#38b6e3"), 3: QColor("#b07ae0")},
    via=QColor("#3ecf70"), pad=QColor("#aab4bd"),
    gate_fill=QColor("#161c24"), gate_edge=QColor("#dfe7ee"), glow=True, bus_socket=3,
)

PCB_DEFAULTS = {
    "Blank": 8.0, "Trace": 14.0, "Corner": 8.0, "Junction": 3.0, "Cross": 1.2,
    "Via": 5.0,
    "Resistor": 3.0, "Capacitor": 2.0, "Electrolytic": 1.6, "Inductor": 1.5,
    "Diode": 2.0, "LED": 2.2, "Crystal": 1.2, "Ferrite": 1.2, "Header": 1.4,
    "Fuse": 2.2, "Transformer": 1.2,
    "IC": 1.6, "QFP IC": 1.0, "Op-Amp": 1.8, "Regulator": 1.6,
    "MCU 2×2": 1.5, "DIP-8 2×1": 1.8, "FPGA 3×3": 0.9,
    "Relay 2×2": 1.0, "Conn 4×1": 1.2, "Osc 2×1": 1.1,
    "Transistor": 2.0, "Test Point": 1.6, "Button": 1.0, "Potentiometer": 1.4,
    "Piezo": 0.8, "Speaker": 1.2, "Motor": 1.4, "USB": 0.7, "Antenna": 0.6,
    "Battery": 1.0,
    "Power Rail": 4.0, "Power Corner": 2.5, "Power T": 1.0, "Power Cross": 0.6,
    "Power Src": 1.6, "Power Tap": 1.2,
    "Gnd Rail": 4.0, "Gnd Corner": 2.5, "Gnd T": 1.0, "Gnd Cross": 0.6,
    "Gnd Symbol": 1.6, "Gnd Tap": 1.2,
    "Mount Hole": 0.9, "Fiducial": 0.8, "Silkscreen": 1.4,
}
LOGIC_DEFAULTS = {
    "Blank": 9.0, "Wire": 16.0, "Corner": 10.0, "T": 3.0, "Cross": 1.2,
    "Via": 5.0, "Switch": 2.2, "LED": 2.2, "GND": 2.0, "VCC": 2.0,
    "NOT": 2.0, "BUF": 1.0, "TRI": 1.2,
    "AND": 2.0, "OR": 2.0, "XOR": 1.4, "XNOR": 1.0, "NAND": 1.0, "NOR": 1.0,
    "MUX": 1.6, "ADD": 1.4, "CMP": 1.2,
    "REG": 2.0, "CTR": 1.4,
    "DEC": 1.0, "ADC": 1.0, "DAC": 1.0, "IO": 1.2, "DRV": 1.4,
    "ALU": 1.2, "RAM": 1.4, "ROM": 1.2, "7-SEG": 1.6,
    "CPU 2×2": 1.5, "SRAM 2×2": 1.3, "GPIO 2×1": 1.5,
    "GPU 2×2": 1.0, "UART 2×1": 1.4, "Timer 2×1": 1.3,
    "Clock Wire": 5.0, "Clock Corner": 3.5, "Clock Src": 1.8, "XTAL": 1.2, "PLL": 1.0,
    "Bus Wire": 4.0, "Bus Corner": 3.0, "Bus T": 1.4, "Bus Cross": 0.5, "Bus Tap": 1.5,
}

PCB_SINGLES = [
    ("Blank", (0, 0, 0, 0), "blank", "X"),
    ("Trace", (1, 0, 1, 0), "trace", "I"),
    ("Corner", (1, 1, 0, 0), "trace", "L"),
    ("Junction", (1, 1, 1, 0), "trace", "T"),
    ("Cross", (1, 1, 1, 1), "trace", "X"),
    ("Via", (1, 0, 0, 0), "via", "S"),
    ("Resistor", (1, 0, 1, 0), "resistor", "I"),
    ("Capacitor", (1, 0, 1, 0), "cap", "I"),
    ("Electrolytic", (1, 0, 1, 0), "elyt", "I"),
    ("Inductor", (1, 0, 1, 0), "inductor", "I"),
    ("Diode", (1, 0, 1, 0), "diode", "I"),
    ("LED", (1, 0, 1, 0), "pcb_led", "I"),
    ("Crystal", (1, 0, 1, 0), "crystal", "I"),
    ("Ferrite", (1, 0, 1, 0), "ferrite", "I"),
    ("Fuse", (1, 0, 1, 0), "fuse", "I"),
    ("Transformer", (1, 0, 1, 0), "transformer", "I"),
    ("Header", (1, 0, 1, 0), "header", "I"),
    ("IC", (1, 0, 1, 0), "chip", "I"),
    ("QFP IC", (1, 1, 1, 1), "qfp", "X"),
    ("Op-Amp", (0, 1, 1, 1), "opamp", "T"),
    ("Regulator", (1, 2, 3, 0), "regulator", "T"),
    ("Transistor", (1, 0, 0, 0), "transistor", "S"),
    ("Test Point", (1, 0, 0, 0), "testpoint", "S"),
    ("Button", (1, 0, 0, 0), "button", "S"),
    ("Potentiometer", (1, 0, 0, 0), "pot", "S"),
    ("Piezo", (1, 0, 0, 0), "piezo", "S"),
    ("Speaker", (1, 0, 0, 0), "speaker", "S"),
    ("Motor", (1, 0, 0, 0), "motor", "S"),
    ("USB", (1, 0, 0, 0), "usb", "S"),
    ("Antenna", (1, 0, 0, 0), "antenna", "S"),
    ("Power Rail", (2, 0, 2, 0), "trace", "I"),
    ("Power Corner", (2, 2, 0, 0), "trace", "L"),
    ("Power T", (2, 2, 2, 0), "trace", "T"),
    ("Power Cross", (2, 2, 2, 2), "trace", "X"),
    ("Power Src", (2, 0, 0, 0), "source", "S"),
    ("Battery", (2, 0, 0, 0), "battery", "S"),
    ("Power Tap", (2, 1, 0, 0), "trace", "L"),
    ("Gnd Rail", (3, 0, 3, 0), "trace", "I"),
    ("Gnd Corner", (3, 3, 0, 0), "trace", "L"),
    ("Gnd T", (3, 3, 3, 0), "trace", "T"),
    ("Gnd Cross", (3, 3, 3, 3), "trace", "X"),
    ("Gnd Symbol", (3, 0, 0, 0), "gndsym", "S"),
    ("Gnd Tap", (3, 1, 0, 0), "trace", "L"),
    ("Mount Hole", (0, 0, 0, 0), "mount", "X"),
    ("Fiducial", (0, 0, 0, 0), "fiducial", "X"),
    ("Silkscreen", (0, 0, 0, 0), "silk", "X"),
]
LOGIC_SINGLES = [
    ("Blank", (0, 0, 0, 0), "blank", "X"),
    ("Wire", (1, 0, 1, 0), "trace", "I"),
    ("Corner", (1, 1, 0, 0), "trace", "L"),
    ("T", (1, 1, 1, 0), "trace", "T"),
    ("Cross", (1, 1, 1, 1), "trace", "X"),
    ("Via", (1, 0, 0, 0), "via", "S"),
    ("Switch", (1, 0, 0, 0), "switch", "S"),
    ("LED", (1, 0, 0, 0), "led", "S"),
    ("GND", (1, 0, 0, 0), "gndsym", "S"),
    ("VCC", (1, 0, 0, 0), "source", "S"),
    ("NOT", (1, 0, 1, 0), "gate_not", "I"),
    ("BUF", (1, 0, 1, 0), "gate_buf", "I"),
    ("TRI", (1, 0, 1, 0), "gate_tri", "I"),
    ("AND", (0, 1, 1, 1), "gate_and", "T"),
    ("OR", (0, 1, 1, 1), "gate_or", "T"),
    ("XOR", (0, 1, 1, 1), "gate_xor", "T"),
    ("XNOR", (0, 1, 1, 1), "gate_xnor", "T"),
    ("NAND", (0, 1, 1, 1), "gate_nand", "T"),
    ("NOR", (0, 1, 1, 1), "gate_nor", "T"),
    ("MUX", (0, 1, 1, 1), "gate_mux", "T"),
    ("ADD", (0, 1, 1, 1), "gate_add", "T"),
    ("CMP", (0, 1, 1, 1), "gate_cmp", "T"),
    ("REG", (2, 1, 0, 1), "gate_reg", "S"),
    ("CTR", (2, 1, 0, 1), "gate_ctr", "S"),
    ("DEC", (0, 1, 1, 3), "gate_dec", "S"),
    ("ADC", (0, 3, 1, 1), "gate_adc", "S"),
    ("DAC", (3, 1, 1, 0), "gate_dac", "S"),
    ("IO", (1, 3, 0, 0), "gate_io", "I"),
    ("DRV", (3, 0, 3, 0), "gate_drv", "I"),
    ("ALU", (0, 3, 1, 1), "gate_alu", "S"),
    ("RAM", (0, 3, 3, 3), "gate_ram", "T"),
    ("ROM", (3, 0, 0, 0), "gate_rom", "S"),
    ("7-SEG", (1, 0, 0, 0), "gate_seg", "S"),
    ("Clock Wire", (2, 0, 2, 0), "trace", "I"),
    ("Clock Corner", (2, 2, 0, 0), "trace", "L"),
    ("Clock Src", (2, 0, 0, 0), "clocksrc", "S"),
    ("XTAL", (2, 0, 0, 0), "xtal", "S"),
    ("PLL", (2, 0, 2, 0), "gate_pll", "I"),
    ("Bus Wire", (3, 0, 3, 0), "trace", "I"),
    ("Bus Corner", (3, 3, 0, 0), "trace", "L"),
    ("Bus T", (3, 3, 3, 0), "trace", "T"),
    ("Bus Cross", (3, 3, 3, 3), "trace", "X"),
    ("Bus Tap", (3, 1, 0, 0), "trace", "L"),
]

FP_SPECS = {
    "pcb": [
        dict(base="MCU 2×2", slug="mcu", w=2, h=2, label="MCU",
             color="#14211a", edge="#4e7a58", prefix="U",
             pins={(0, 0): {N: 2}, (0, 1): {S: 1}, (1, 1): {S: 1}}),
        dict(base="DIP-8 2×1", slug="dip", w=2, h=1, label="DIP8",
             color="#1a1d24", edge="#5a6a7a", prefix="U",
             pins={(0, 0): {N: 1, S: 1}, (1, 0): {N: 1, S: 1}}),
        dict(base="FPGA 3×3", slug="fpga", w=3, h=3, label="FPGA",
             color="#191427", edge="#6a5a9a", prefix="U",
             pins={(0, 2): {S: 1}, (1, 2): {S: 1}, (2, 2): {S: 1}, (1, 0): {N: 2}}),
        dict(base="Relay 2×2", slug="relay", w=2, h=2, label="RLY",
             color="#241a14", edge="#8a6a4a", prefix="K",
             pins={(0, 0): {N: 1}, (1, 0): {N: 1},
                   (0, 1): {S: 2}, (1, 1): {S: 2}}),
        dict(base="Conn 4×1", slug="conn4", w=4, h=1, label="CONN",
             color="#101820", edge="#4a6a8a", prefix="J",
             pins={(0, 0): {S: 1}, (1, 0): {S: 1}, (2, 0): {S: 1}, (3, 0): {S: 1}}),
        dict(base="Osc 2×1", slug="osc", w=2, h=1, label="OSC",
             color="#1a1a1a", edge="#8a8a5a", prefix="X",
             pins={(0, 0): {W: 2}, (1, 0): {E: 1}}),
    ],
    "logic": [
        dict(base="CPU 2×2", slug="cpu", w=2, h=2, label="CPU",
             color="#101b26", edge="#3f6a8a", prefix="U",
             pins={(0, 0): {N: 2}, (1, 0): {E: 3}, (0, 1): {S: 1}, (1, 1): {S: 1}}),
        dict(base="SRAM 2×2", slug="sram", w=2, h=2, label="SRAM",
             color="#161020", edge="#7a5a9a", prefix="U",
             pins={(0, 1): {W: 3}, (1, 1): {E: 3}, (1, 0): {N: 2}}),
        dict(base="GPIO 2×1", slug="gpio", w=2, h=1, label="GPIO",
             color="#101d1a", edge="#3f7a6a", prefix="U",
             pins={(0, 0): {W: 3, N: 1}, (1, 0): {E: 1, N: 1}}),
        dict(base="GPU 2×2", slug="gpu", w=2, h=2, label="GPU",
             color="#1d1020", edge="#8a5a9a", prefix="U",
             pins={(0, 0): {N: 2}, (0, 1): {W: 3}, (1, 1): {E: 3}, (1, 0): {S: 1}}),
        dict(base="UART 2×1", slug="uart", w=2, h=1, label="UART",
             color="#0f1d17", edge="#3f8a5a", prefix="U",
             pins={(0, 0): {W: 1}, (1, 0): {E: 1}}),
        dict(base="Timer 2×1", slug="timer", w=2, h=1, label="TMR",
             color="#1d1a0f", edge="#8a7a3f", prefix="U",
             pins={(0, 0): {W: 2}, (1, 0): {E: 1}}),
    ],
}

BUILTIN = {
    "PCB board": TilesetDef("PCB board", "pcb", PCB_THEME,
                            {1: "signal", 2: "power", 3: "gnd"}, 0,
                            PCB_SINGLES, FP_SPECS["pcb"], PCB_DEFAULTS),
    "Logic circuit": TilesetDef("Logic circuit", "logic", LOGIC_THEME,
                                {1: "signal", 2: "clock", 3: "bus"}, 3,
                                LOGIC_SINGLES, FP_SPECS["logic"], LOGIC_DEFAULTS),
}

KIND_PREFIX = {
    "resistor": "R", "cap": "C", "elyt": "C", "inductor": "L", "diode": "D",
    "pcb_led": "D", "led": "D", "crystal": "X", "xtal": "X", "ferrite": "FB",
    "header": "J", "chip": "U", "qfp": "U", "transistor": "Q", "testpoint": "TP",
    "button": "SW", "switch": "SW", "piezo": "BZ", "usb": "J", "antenna": "AN",
    "fuse": "F", "transformer": "T", "motor": "M", "speaker": "LS", "opamp": "U",
    "regulator": "U", "battery": "BT", "pot": "RV", "clocksrc": "U",
}
BASE_PREFIX = dict(KIND_PREFIX)
COMP_KINDS = set(KIND_PREFIX) | {
    "gate_and", "gate_nand", "gate_or", "gate_nor", "gate_xor", "gate_xnor",
    "gate_not", "gate_buf", "gate_mux", "gate_add", "gate_cmp", "gate_reg",
    "gate_ctr", "gate_dec", "gate_adc", "gate_dac", "gate_io", "gate_drv",
    "gate_tri", "gate_pll", "gate_alu", "gate_ram", "gate_rom", "gate_seg"}
NON_BOM_KINDS = {"blank", "trace", "via", "mount", "silk", "fiducial",
                 "gndsym", "source"}
BASE_NON_BOM = set(NON_BOM_KINDS)
FP_INFO = {}
FP_ANCHOR_KINDS = set()
FP_ACTIVE = {"cpu", "gpu", "uart", "timer", "osc"}


def _reset_fp_globals():
    FP_INFO.clear()
    FP_ANCHOR_KINDS.clear()
    NON_BOM_KINDS.clear()
    NON_BOM_KINDS.update(BASE_NON_BOM)
    KIND_PREFIX.clear()
    KIND_PREFIX.update(BASE_PREFIX)


# ---- zone profiles ----------------------------------------------------------

def kind_class(kind):
    if kind == "blank":
        return "blank"
    if kind in ("trace", "via", "mount", "silk", "fiducial"):
        return "trace"
    if kind.startswith("fp_"):
        return "fp"
    if kind.startswith("gate_") or kind in ("chip", "qfp", "opamp", "regulator"):
        return "ic"
    if kind in ("resistor", "cap", "elyt", "inductor", "diode", "pcb_led",
                "crystal", "ferrite", "fuse", "transformer"):
        return "passive"
    if kind in ("header", "usb", "button", "switch", "testpoint", "pot", "piezo",
                "speaker", "motor", "antenna", "led", "xtal", "battery"):
        return "io"
    if kind in ("source", "gndsym", "clocksrc"):
        return "source"
    return "other"


ZONE_PROFILES = {
    "Digital: ICs ×4": {"blank": 0.8, "trace": 0.9, "passive": 0.4, "ic": 4.0,
                        "fp": 4.0, "io": 1.0, "source": 1.0, "other": 1.0},
    "Analog: passives ×3": {"blank": 0.9, "trace": 1.2, "passive": 3.0, "ic": 0.15,
                            "fp": 0.15, "io": 1.5, "source": 1.0, "other": 1.0},
    "Power: sources ×3": {"blank": 0.8, "trace": 1.6, "passive": 0.8, "ic": 0.5,
                          "fp": 0.5, "io": 0.8, "source": 3.0, "other": 1.0},
    "Routing: traces ×2.5": {"blank": 0.6, "trace": 2.5, "passive": 0.7, "ic": 0.7,
                             "fp": 0.7, "io": 0.7, "source": 0.7, "other": 1.0},
    "Clear: mostly blank": {"blank": 6.0, "trace": 0.12, "passive": 0.12, "ic": 0.05,
                            "fp": 0.05, "io": 0.12, "source": 0.12, "other": 0.12},
}
ZONE_COLORS = {
    "Digital: ICs ×4": "#3aa0ff", "Analog: passives ×3": "#ffb03a",
    "Power: sources ×3": "#ff5a4a", "Routing: traces ×2.5": "#4ad0a0",
    "Clear: mostly blank": "#9aa4ae",
}


# ---- footprint construction --------------------------------------------------

def _rot_grid(w, h, grid, r):
    g = [[list(c) for c in row] for row in grid]
    ww, hh = w, h
    for _ in range(r % 4):
        ng = [[[0, 0, 0, 0] for _ in range(hh)] for _ in range(ww)]
        for y in range(hh):
            for x in range(ww):
                e = g[y][x]
                ne = (e[3], e[0], e[1], e[2])
                nx, ny = hh - 1 - y, x
                ng[ny][nx] = ne
        g = ng
        ww, hh = hh, ww
    return ww, hh, g


def add_footprint(tiles, spec, bw, ctr):
    w, h = spec["w"], spec["h"]
    base, slug = spec["base"], spec["slug"]
    weight = bw.get(base, 1.0) / (w * h * 4.0)
    grid = [[[0, 0, 0, 0] for _ in range(w)] for _ in range(h)]
    for cy in range(h):
        for cx in range(w):
            for d, sk in spec.get("pins", {}).get((cx, cy), {}).items():
                grid[cy][cx][d] = sk
    for r in range(4):
        sid = next(ctr)
        w2, h2, g2 = _rot_grid(w, h, grid, r)
        for y in range(h2):
            for x in range(w2):
                e = g2[y][x]
                for cy2 in range(h2):        # seams between sibling cells
                    for cx2 in range(w2):
                        pass
        # mark internal seams with the unique socket id
        for y in range(h2):
            for x in range(w2):
                e = g2[y][x]
                for d in range(4):
                    nx, ny = x + DIRS[d][0], y + DIRS[d][1]
                    inside = 0 <= nx < w2 and 0 <= ny < h2
                    if inside and e[d] == 0 and g2[ny][nx][OPP[d]] == 0:
                        # only convert edges that belong to the footprint body:
                        # a seam edge is one whose opposite counterpart cell is a
                        # sibling AND the edge was a seam in the unrotated grid.
                        pass
        for y in range(h2):
            for x in range(w2):
                e = g2[y][x]
                for d in range(4):
                    if e[d] == 0:
                        nx, ny = x + DIRS[d][0], y + DIRS[d][1]
                        if 0 <= nx < w2 and 0 <= ny < h2 and g2[ny][nx][OPP[d]] == 0:
                            e[d] = sid
                            g2[ny][nx][OPP[d]] = sid
        for y in range(h2):
            for x in range(w2):
                kind = f"fp_{slug}" if (x, y) == (0, 0) else f"fp_{slug}_{x}_{y}"
                edges = tuple(g2[y][x])
                tiles.append(Tile(base, edges, edges, kind, weight, r))
    FP_INFO[base] = dict(w=w, h=h, slug=slug, label=spec["label"],
                         color=spec.get("color", "#151a21"),
                         edge=spec.get("edge", "#5a6a7a"),
                         label_cell=(w // 2, h // 2))
    anchor = f"fp_{slug}"
    FP_ANCHOR_KINDS.add(anchor)
    COMP_KINDS.add(anchor)
    KIND_PREFIX[anchor] = spec.get("prefix", "U")
    for cy in range(h):
        for cx in range(w):
            if (cx, cy) != (0, 0):
                NON_BOM_KINDS.add(f"fp_{slug}_{cx}_{cy}")


def fp_cell(kind):
    if kind in FP_ANCHOR_KINDS:
        return (0, 0)
    parts = kind.rsplit("_", 2)
    return int(parts[-2]), int(parts[-1])


def fp_dims(base, rot):
    info = FP_INFO[base]
    w, h = info["w"], info["h"]
    return (h, w) if rot % 2 else (w, h)


def fp_label_cell(base, rot):
    info = FP_INFO[base]
    lx, ly = info["label_cell"]
    w, h = info["w"], info["h"]
    for _ in range(rot % 4):
        lx, ly = h - 1 - ly, lx
        w, h = h, w
    return lx, ly


def build_tiles(defn, bw):
    """Build all rotated tile variants from a TilesetDef.
    Adjacency rule: two edges may touch iff sockets are equal."""
    _reset_fp_globals()
    tiles = []
    ctr = count(INNER_BASE)
    for base, edges, kind, sym in defn.singles:
        n = {"X": 1, "I": 2, "L": 4, "T": 4, "S": 4}.get(sym, 1)
        w = bw.get(base, 1.0) / n
        for r in range(n):
            e = edges
            for _ in range(r):
                e = (e[3], e[0], e[1], e[2])
            tiles.append(Tile(base, e, edges, kind, w, r))
    for spec in defn.fps:
        add_footprint(tiles, spec, bw, ctr)
    return tiles


# ---- tileset JSON round-trip --------------------------------------------------

def tileset_from_dict(d, name_fallback="Custom"):
    name = str(d.get("name", name_fallback))
    flavor = d.get("flavor", "pcb")
    flavor = flavor if flavor in ("pcb", "logic") else "pcb"
    th = d.get("theme", {})

    def col(key, alt):
        return QColor(th.get(key, alt))

    grid = QColor(th.get("grid", "#ffffff"))
    grid.setAlpha(int(th.get("grid_alpha", 14)))
    sockets = {}
    for k, v in (d.get("sockets") or {}).items():
        sockets[int(k)] = QColor(v)
    for sid, c in ((1, "#3ecf70"), (2, "#38b6e3"), (3, "#b07ae0")):
        sockets.setdefault(sid, QColor(c))
    theme = Theme(bg=col("bg", "#0d1117"), cell=col("cell", "#141b22"), grid=grid,
                  sockets=sockets, via=col("via", "#3ecf70"),
                  pad=col("pad", "#aab4bd"), gate_fill=col("gate_fill", "#161c24"),
                  gate_edge=col("gate_edge", "#dfe7ee"),
                  glow=bool(d.get("glow", False)), bus_socket=int(d.get("bus_socket", 3)))
    singles = []
    for t in d.get("tiles", []):
        base = str(t["base"])
        edges = tuple(int(x) for x in t["edges"])
        if len(edges) != 4:
            raise ValueError(f"tile '{base}': edges needs 4 entries")
        kind = str(t.get("kind", "trace"))
        sym = str(t.get("sym", "X")).upper()
        if sym not in "XILTS":
            sym = "X"
        singles.append((base, edges, kind, sym))
    if not singles:
        raise ValueError("tileset has no tiles")
    maxs = max(max(e) for _, e, _, _ in singles)
    if any(s > maxs or s < 0 for _, e, _, _ in singles for s in e):
        raise ValueError("bad socket id")
    fps = []
    for f in d.get("footprints", []):
        pins = {}
        for kk, dd in (f.get("pins") or {}).items():
            cx, cy = (int(x) for x in str(kk).split(","))
            pins[(cx, cy)] = {DIRL.index(dr): int(sv) for dr, sv in dd.items()}
        fps.append(dict(base=str(f["base"]), slug=str(f.get("slug", f["base"])),
                        w=int(f["w"]), h=int(f["h"]), label=str(f.get("label", f["base"])),
                        color=f.get("color", "#151a21"), edge=f.get("edge", "#5a6a7a"),
                        prefix=str(f.get("prefix", "U")), pins=pins))
    for gk, gv in (d.get("gates") or {}).items():
        shape = gv[3] if len(gv) > 3 and gv[3] in ("rect", "trap", "seg") else "rect"
        GATE_STYLE[str(gk)] = (str(gv[0]), bool(gv[1]), int(gv[2]) % 4, shape)
    weights = {str(k): float(v) for k, v in (d.get("weights") or {}).items()}
    snames = {int(k): str(v) for k, v in (d.get("socket_names") or {}).items()}
    if not snames:
        snames = {1: "signal", 2: "clock" if flavor == "logic" else "power",
                  3: "bus" if flavor == "logic" else "gnd"}
    return TilesetDef(name, flavor, theme, snames, int(d.get("bus_socket", 3)),
                      singles, fps, weights)


def tileset_to_dict(defn, weights):
    th = defn.theme
    tiles = [{"base": b, "edges": list(e), "kind": k, "sym": s,
              "weight": round(weights.get(b, 1.0), 2)}
             for b, e, k, s in defn.singles]
    fps = []
    for f in defn.fps:
        pins = {f"{cx},{cy}": {DIRL[d]: sv for d, sv in pd.items()}
                for (cx, cy), pd in f.get("pins", {}).items()}
        fps.append({"base": f["base"], "slug": f["slug"], "w": f["w"], "h": f["h"],
                    "label": f["label"], "color": f.get("color"),
                    "edge": f.get("edge"), "prefix": f.get("prefix", "U"),
                    "pins": pins})
    d = {"app": "wfc-tileset", "version": 1, "name": defn.name,
         "flavor": defn.flavor, "bus_socket": defn.bus_socket, "glow": th.glow,
         "sockets": {str(k): c.name() for k, c in th.sockets.items()},
         "socket_names": {str(k): v for k, v in defn.socket_names.items()},
         "theme": {"bg": th.bg.name(), "cell": th.cell.name(), "grid": "#ffffff",
                   "grid_alpha": th.grid.alpha(), "via": th.via.name(),
                   "pad": th.pad.name(), "gate_fill": th.gate_fill.name(),
                   "gate_edge": th.gate_edge.name()},
         "tiles": tiles, "footprints": fps,
         "weights": {k: round(v, 2) for k, v in weights.items()}}
    return d


# --------------------------------------------------------------------------- tile painting

GATE_STYLE = {
    "gate_and": ("&", False, 1, "rect"), "gate_nand": ("&", True, 1, "rect"),
    "gate_or": ("\u22651", False, 1, "rect"), "gate_nor": ("\u22651", True, 1, "rect"),
    "gate_xor": ("=1", False, 1, "rect"), "gate_xnor": ("=1", True, 1, "rect"),
    "gate_not": ("1", True, 0, "rect"), "gate_buf": ("1", False, 0, "rect"),
    "gate_tri": ("TRI", False, 0, "rect"),
    "gate_mux": ("MUX", False, 1, "trap"), "gate_add": ("\u03a3", False, 1, "rect"),
    "gate_cmp": ("CMP", False, 1, "rect"),
    "gate_reg": ("REG", False, 1, "rect"), "gate_ctr": ("CTR", False, 1, "rect"),
    "gate_dec": ("DEC", False, 1, "rect"), "gate_adc": ("ADC", False, 1, "rect"),
    "gate_dac": ("DAC", False, 1, "rect"), "gate_io": ("IO", False, 1, "rect"),
    "gate_drv": ("DRV", False, 1, "rect"), "gate_pll": ("PLL", False, 1, "rect"),
    "gate_alu": ("ALU", False, 1, "rect"), "gate_ram": ("RAM", False, 1, "rect"),
    "gate_rom": ("ROM", False, 1, "rect"), "gate_seg": ("8.", False, 0, "seg"),
}

VERILOG_PRIM = {"gate_and": "and", "gate_nand": "nand", "gate_or": "or",
                "gate_nor": "nor", "gate_xor": "xor", "gate_xnor": "xnor",
                "gate_not": "not", "gate_buf": "buf"}


def _pen(color, w):
    pen = QPen(color)
    pen.setWidthF(max(w, 0.8))
    pen.setCapStyle(Qt.RoundCap)
    pen.setJoinStyle(Qt.RoundJoin)
    return pen


def _lead(p, path, color, lw):
    p.setBrush(Qt.NoBrush)
    p.setPen(_pen(QColor(color).darker(165), lw * 1.55))
    p.drawPath(path)
    p.setPen(_pen(color, lw))
    p.drawPath(path)


def _ring(p, c, r_out, r_in, color):
    p.setBrush(QColor(color))
    p.setPen(_pen(QColor(color).darker(150), r_out * 0.4))
    p.drawEllipse(c, r_out, r_out)
    p.setBrush(QColor(8, 10, 9))
    p.setPen(Qt.NoPen)
    p.drawEllipse(c, r_in, r_in)


def draw_trace(p, edges, theme, s):
    conns = [d for d in range(4) if edges[d]]
    if not conns:
        return
    c = QPointF(s / 2, s / 2)
    mids = (QPointF(s / 2, 0), QPointF(s, s / 2), QPointF(s / 2, s), QPointF(0, s / 2))
    lw = max(2.0, 0.15 * s)
    bus = getattr(theme, "bus_socket", 0)

    def col(d):
        return theme.sockets.get(edges[d], theme.via)

    all_bus = bool(bus) and all(edges[d] == bus for d in conns)
    segs = []
    if len(conns) == 2:
        a, b = conns
        ca, cb = col(a), col(b)
        if ca == cb:
            path = QPainterPath(mids[a])
            if (a + 2) % 4 == b:
                path.lineTo(mids[b])
            else:
                path.quadTo(c, mids[b])
            segs.append((path, ca))
        else:
            p1 = QPainterPath(mids[a]); p1.lineTo(c); segs.append((p1, ca))
            p2 = QPainterPath(c); p2.lineTo(mids[b]); segs.append((p2, cb))
    else:
        for d in conns:
            path = QPainterPath(c); path.lineTo(mids[d])
            segs.append((path, col(d)))

    if all_bus:
        for path, cc in segs:
            p.setPen(_pen(cc, lw * 2.3)); p.setBrush(Qt.NoBrush); p.drawPath(path)
        if len(conns) >= 3:
            p.setBrush(segs[0][1]); p.setPen(Qt.NoPen)
            p.drawEllipse(c, lw * 1.15, lw * 1.15)
        for path, _ in segs:
            p.setPen(_pen(theme.bg, lw * 0.75)); p.drawPath(path)
        if len(conns) >= 3:
            p.setBrush(theme.bg); p.setPen(Qt.NoPen)
            p.drawEllipse(c, lw * 0.38, lw * 0.38)
        return

    for path, cc in segs:
        p.setPen(_pen(QColor(cc).darker(165), lw * 1.55)); p.setBrush(Qt.NoBrush); p.drawPath(path)
    for path, cc in segs:
        p.setPen(_pen(cc, lw)); p.drawPath(path)
    if len({edges[d] for d in conns}) > 1:
        _ring(p, c, 0.16 * s, 0.06 * s, theme.via)


def draw_via(p, theme, s):
    c = QPointF(s / 2, s / 2)
    path = QPainterPath(QPointF(s / 2, 0)); path.lineTo(c)
    _lead(p, path, theme.via, max(2.0, 0.13 * s))
    _ring(p, c, 0.20 * s, 0.075 * s, theme.via)


def _vleads(p, theme, s):
    c = s / 2
    col = theme.sockets.get(1, theme.via)
    path = QPainterPath(QPointF(c, 0))
    path.lineTo(c, 0.36 * s)
    path.moveTo(c, s)
    path.lineTo(c, 0.64 * s)
    _lead(p, path, col, max(2.0, 0.13 * s))
    p.setBrush(QColor(theme.pad))
    p.setPen(_pen(QColor(theme.pad).darker(160), 1.0))
    for yy in (0.12 * s, 0.88 * s):
        p.drawEllipse(QPointF(c, yy), 0.105 * s, 0.105 * s)


def draw_resistor(p, theme, s):
    _vleads(p, theme, s)
    c = s / 2
    p.setBrush(QColor("#d8c69b")); p.setPen(_pen(QColor("#5e5138"), 1.2))
    p.drawRoundedRect(QRectF(c - 0.15 * s, 0.34 * s, 0.30 * s, 0.32 * s), 0.05 * s, 0.05 * s)
    for col, yy in (("#7c5a33", 0.40), ("#a8433a", 0.48), ("#b8863b", 0.56)):
        p.fillRect(QRectF(c - 0.15 * s, yy * s, 0.30 * s, 0.05 * s), QColor(col))


def draw_cap(p, theme, s):
    _vleads(p, theme, s)
    c = s / 2
    p.setBrush(QColor("#cf8a3f")); p.setPen(_pen(QColor("#7a4d1e"), 1.2))
    p.drawEllipse(QPointF(c, s / 2), 0.16 * s, 0.16 * s)


def draw_elyt(p, theme, s):
    _vleads(p, theme, s)
    c = s / 2
    p.setBrush(QColor("#25324a")); p.setPen(_pen(QColor("#141c2b"), 1.2))
    p.drawRoundedRect(QRectF(c - 0.14 * s, 0.30 * s, 0.28 * s, 0.40 * s), 0.05 * s, 0.05 * s)
    p.fillRect(QRectF(c - 0.14 * s, 0.30 * s, 0.06 * s, 0.40 * s), QColor("#c8d2dc"))
    p.fillRect(QRectF(c + 0.02 * s, 0.44 * s, 0.10 * s, 0.04 * s), QColor("#c8d2dc"))
    p.fillRect(QRectF(c + 0.02 * s, 0.52 * s, 0.10 * s, 0.04 * s), QColor("#c8d2dc"))


def draw_inductor(p, theme, s):
    _vleads(p, theme, s)
    c = s / 2
    p.setBrush(QColor("#2e3a4a")); p.setPen(_pen(QColor("#1d2632"), 1.2))
    p.drawRoundedRect(QRectF(c - 0.15 * s, 0.34 * s, 0.30 * s, 0.32 * s), 0.05 * s, 0.05 * s)
    p.setBrush(Qt.NoBrush); p.setPen(_pen(QColor("#9fb4c8"), 1.1))
    for i in range(3):
        yy = 0.39 + 0.09 * i
        p.drawArc(QRectF(c - 0.10 * s, yy * s, 0.20 * s, 0.07 * s), 0, 180 * 16)


def draw_diode(p, theme, s):
    _vleads(p, theme, s)
    c = s / 2
    p.setBrush(QColor("#1a1d22")); p.setPen(_pen(QColor("#3c424b"), 1.2))
    p.drawRoundedRect(QRectF(c - 0.14 * s, 0.34 * s, 0.28 * s, 0.32 * s), 0.04 * s, 0.04 * s)
    p.fillRect(QRectF(c - 0.14 * s, 0.57 * s, 0.28 * s, 0.06 * s), QColor("#c9ced6"))


def draw_pcb_led(p, theme, s):
    _vleads(p, theme, s)
    c = s / 2
    p.setBrush(QColor(226, 80, 60, 50)); p.setPen(Qt.NoPen)
    p.drawEllipse(QPointF(c, s / 2), 0.20 * s, 0.20 * s)
    tri = QPainterPath(QPointF(c - 0.08 * s, 0.40 * s))
    tri.lineTo(QPointF(c + 0.08 * s, 0.40 * s))
    tri.lineTo(QPointF(c, 0.52 * s))
    tri.closeSubpath()
    p.setBrush(QColor("#e2503c")); p.setPen(_pen(QColor("#f4d7d0"), 1.0))
    p.drawPath(tri)
    p.setPen(_pen(QColor("#f4d7d0"), 1.2))
    p.drawLine(QPointF(c - 0.08 * s, 0.54 * s), QPointF(c + 0.08 * s, 0.54 * s))


def draw_crystal(p, theme, s):
    _vleads(p, theme, s)
    c = s / 2
    p.setBrush(QColor("#b9c4cc")); p.setPen(_pen(QColor("#6d7a85"), 1.2))
    p.drawRoundedRect(QRectF(c - 0.13 * s, 0.33 * s, 0.26 * s, 0.34 * s), 0.10 * s, 0.10 * s)


def draw_ferrite(p, theme, s):
    _vleads(p, theme, s)
    c = s / 2
    p.setBrush(QColor("#23262b")); p.setPen(_pen(QColor("#0f1114"), 1.2))
    p.drawRoundedRect(QRectF(c - 0.15 * s, 0.34 * s, 0.30 * s, 0.32 * s), 0.05 * s, 0.05 * s)
    p.fillRect(QRectF(c - 0.15 * s, 0.47 * s, 0.30 * s, 0.06 * s), QColor("#5a6470"))


def draw_fuse(p, theme, s):
    _vleads(p, theme, s)
    c = s / 2
    p.setBrush(QColor("#d9dee3")); p.setPen(_pen(QColor("#8a939c"), 1.2))
    p.drawRoundedRect(QRectF(c - 0.12 * s, 0.33 * s, 0.24 * s, 0.34 * s), 0.10 * s, 0.10 * s)
    p.setBrush(Qt.NoBrush); p.setPen(_pen(QColor("#4a525b"), 1.1))
    path = QPainterPath(QPointF(c, 0.38 * s))
    path.cubicTo(QPointF(c - 0.07 * s, 0.45 * s), QPointF(c + 0.07 * s, 0.55 * s), QPointF(c, 0.62 * s))
    p.drawPath(path)


def draw_transformer(p, theme, s):
    _vleads(p, theme, s)
    c = s / 2
    p.setBrush(QColor("#2c3240")); p.setPen(_pen(QColor("#171c26"), 1.2))
    p.drawRoundedRect(QRectF(c - 0.16 * s, 0.32 * s, 0.32 * s, 0.36 * s), 0.04 * s, 0.04 * s)
    p.setBrush(Qt.NoBrush); p.setPen(_pen(QColor("#c8a24d"), 1.1))
    p.drawEllipse(QRectF(c - 0.13 * s, 0.38 * s, 0.10 * s, 0.24 * s))
    p.drawEllipse(QRectF(c + 0.03 * s, 0.38 * s, 0.10 * s, 0.24 * s))
    p.setPen(_pen(QColor("#9aa6b2"), 1.4))
    p.drawLine(QPointF(c, 0.36 * s), QPointF(c, 0.64 * s))


def draw_header(p, theme, s):
    _vleads(p, theme, s)
    c = s / 2
    p.setBrush(QColor("#14171c")); p.setPen(_pen(QColor("#333a44"), 1.2))
    p.drawRect(QRectF(c - 0.13 * s, 0.32 * s, 0.26 * s, 0.36 * s))
    p.setBrush(QColor("#e0b64f")); p.setPen(_pen(QColor("#8a6c22"), 1.0))
    for yy in (0.40, 0.58):
        p.drawRect(QRectF(c - 0.035 * s, yy * s, 0.07 * s, 0.10 * s))


def draw_chip(p, theme, s):
    _vleads(p, theme, s)
    c = s / 2
    x0, x1 = c - 0.18 * s, c + 0.18 * s
    p.setPen(_pen(QColor("#b7c0c8"), max(1.4, 0.05 * s)))
    for yy in (0.38, 0.50, 0.62):
        p.drawLine(QPointF(x0 - 0.06 * s, yy * s), QPointF(x0, yy * s))
        p.drawLine(QPointF(x1, yy * s), QPointF(x1 + 0.06 * s, yy * s))
    p.setBrush(QColor("#12151c")); p.setPen(_pen(QColor("#3d4552"), 1.2))
    p.drawRoundedRect(QRectF(x0, 0.30 * s, 0.36 * s, 0.40 * s), 0.03 * s, 0.03 * s)
    p.setBrush(QColor("#b7c0c8")); p.setPen(Qt.NoPen)
    p.drawEllipse(QPointF(c - 0.10 * s, 0.36 * s), 0.02 * s, 0.02 * s)


def draw_qfp(p, theme, s):
    c = s / 2
    p.setBrush(QColor("#12151c")); p.setPen(_pen(QColor("#4a545f"), 1.2))
    p.drawRoundedRect(QRectF(c - 0.20 * s, c - 0.20 * s, 0.40 * s, 0.40 * s), 0.04 * s, 0.04 * s)
    p.setBrush(QColor("#b7c0c8")); p.setPen(Qt.NoPen)
    p.drawEllipse(QPointF(c - 0.10 * s, c - 0.10 * s), 0.025 * s, 0.025 * s)
    p.setPen(_pen(QColor("#c9ced6"), 1.0))
    for k in (-1, 0, 1):
        off = k * 0.11 * s
        p.drawLine(QPointF(c + off, c - 0.20 * s), QPointF(c + off, c - 0.26 * s))
        p.drawLine(QPointF(c + off, c + 0.20 * s), QPointF(c + off, c + 0.26 * s))
        p.drawLine(QPointF(c - 0.20 * s, c + off), QPointF(c - 0.26 * s, c + off))
        p.drawLine(QPointF(c + 0.20 * s, c + off), QPointF(c + 0.26 * s, c + off))


def draw_opamp(p, theme, s):
    p.setBrush(theme.gate_fill); p.setPen(_pen(theme.gate_edge, max(1.4, 0.05 * s)))
    tri = QPainterPath(QPointF(0.22 * s, 0.24 * s))
    tri.lineTo(QPointF(0.22 * s, 0.76 * s))
    tri.lineTo(QPointF(0.78 * s, 0.50 * s))
    tri.closeSubpath()
    p.drawPath(tri)
    f = QFont(); f.setPixelSize(max(6, int(0.16 * s))); f.setBold(True)
    p.setFont(f); p.setPen(QPen(theme.gate_edge))
    p.drawText(QRectF(0.20 * s, 0.24 * s, 0.36 * s, 0.52 * s), Qt.AlignCenter, "\u221e")


def draw_regulator(p, edges, theme, s):
    c = s / 2
    mids = (QPointF(c, 0), QPointF(s, c), QPointF(c, s), QPointF(0, c))
    for d in range(3):
        if edges[d]:
            cc = theme.sockets.get(edges[d], theme.via)
            path = QPainterPath(mids[d]); path.lineTo(QPointF(c, c))
            _lead(p, path, cc, max(2.0, 0.13 * s))
    p.setBrush(QColor("#14181f")); p.setPen(_pen(QColor("#4a545f"), 1.2))
    p.drawRect(QRectF(c - 0.15 * s, c - 0.15 * s, 0.30 * s, 0.30 * s))
    f = QFont(); f.setPixelSize(max(5, int(0.11 * s))); f.setBold(True)
    p.setFont(f); p.setPen(QPen(QColor("#dfe7ee")))
    p.drawText(QRectF(c - 0.15 * s, c - 0.15 * s, 0.30 * s, 0.30 * s), Qt.AlignCenter, "78")


def draw_transistor(p, theme, s):
    c = s / 2
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.32 * s)
    _lead(p, path, theme.sockets.get(1, theme.via), max(2.0, 0.13 * s))
    p.setBrush(QColor("#171a20")); p.setPen(_pen(QColor("#454d58"), 1.1))
    p.drawRoundedRect(QRectF(c - 0.16 * s, 0.32 * s, 0.32 * s, 0.34 * s), 0.04 * s, 0.04 * s)
    p.setBrush(QColor("#c9b06a")); p.setPen(Qt.NoPen)
    for xx in (c - 0.09 * s, c, c + 0.09 * s):
        p.drawRect(QRectF(xx - 0.012 * s, 0.62 * s, 0.024 * s, 0.05 * s))


def draw_testpoint(p, theme, s):
    c = s / 2
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.38 * s)
    _lead(p, path, theme.sockets.get(1, theme.via), max(2.0, 0.13 * s))
    p.setBrush(QColor(theme.pad)); p.setPen(_pen(QColor("#e8b23c"), 1.4))
    p.drawRect(QRectF(c - 0.12 * s, 0.38 * s, 0.24 * s, 0.24 * s))


def draw_button(p, theme, s):
    c = s / 2
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.30 * s)
    _lead(p, path, theme.sockets.get(1, theme.via), max(2.0, 0.13 * s))
    p.setBrush(QColor("#2c333d")); p.setPen(_pen(QColor("#8b97a5"), 1.2))
    p.drawRoundedRect(QRectF(c - 0.14 * s, 0.30 * s, 0.28 * s, 0.30 * s), 0.05 * s, 0.05 * s)
    p.setBrush(QColor("#d7dde3")); p.setPen(_pen(QColor("#7c8894"), 1.0))
    p.drawEllipse(QPointF(c, 0.45 * s), 0.07 * s, 0.07 * s)


def draw_pot(p, theme, s):
    c = s / 2
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.42 * s)
    _lead(p, path, theme.sockets.get(1, theme.via), max(2.0, 0.13 * s))
    p.setBrush(QColor("#2c333d")); p.setPen(_pen(QColor("#8b97a5"), 1.2))
    p.drawEllipse(QPointF(c, 0.60 * s), 0.16 * s, 0.16 * s)
    p.setPen(_pen(QColor("#e3b23c"), 1.6))
    p.drawLine(QPointF(c, 0.60 * s), QPointF(c + 0.11 * s, 0.50 * s))


def draw_piezo(p, theme, s):
    c = s / 2
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.34 * s)
    _lead(p, path, theme.sockets.get(1, theme.via), max(2.0, 0.13 * s))
    p.setBrush(QColor("#14171c")); p.setPen(_pen(QColor("#3a424d"), 1.2))
    p.drawEllipse(QPointF(c, 0.56 * s), 0.17 * s, 0.17 * s)
    p.setBrush(QColor("#0a0c10")); p.setPen(Qt.NoPen)
    p.drawEllipse(QPointF(c, 0.56 * s), 0.055 * s, 0.055 * s)


def draw_speaker(p, theme, s):
    c = s / 2
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.36 * s)
    _lead(p, path, theme.sockets.get(1, theme.via), max(2.0, 0.13 * s))
    p.setBrush(QColor("#8f9aa6")); p.setPen(_pen(QColor("#59626d"), 1.0))
    p.drawRect(QRectF(c - 0.11 * s, 0.36 * s, 0.09 * s, 0.18 * s))
    horn = QPainterPath(QPointF(c - 0.02 * s, 0.40 * s))
    horn.lineTo(QPointF(c + 0.15 * s, 0.28 * s))
    horn.lineTo(QPointF(c + 0.15 * s, 0.66 * s))
    horn.lineTo(QPointF(c - 0.02 * s, 0.54 * s))
    horn.closeSubpath()
    p.drawPath(horn)


def draw_motor(p, theme, s):
    c = s / 2
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.30 * s)
    _lead(p, path, theme.sockets.get(1, theme.via), max(2.0, 0.13 * s))
    p.setBrush(QColor("#1d2127")); p.setPen(_pen(QColor("#4a545f"), 1.2))
    p.drawEllipse(QPointF(c, 0.56 * s), 0.20 * s, 0.20 * s)
    f = QFont(); f.setPixelSize(max(7, int(0.20 * s))); f.setBold(True)
    p.setFont(f); p.setPen(QPen(QColor("#dfe7ee")))
    p.drawText(QRectF(0, 0.30 * s, s, 0.52 * s), Qt.AlignCenter, "M")


def draw_usb(p, theme, s):
    c = s / 2
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.22 * s)
    _lead(p, path, theme.sockets.get(1, theme.via), max(2.0, 0.13 * s))
    p.setBrush(QColor("#8f9aa6")); p.setPen(_pen(QColor("#5a636e"), 1.2))
    p.drawRoundedRect(QRectF(c - 0.17 * s, 0.22 * s, 0.34 * s, 0.52 * s), 0.03 * s, 0.03 * s)
    p.setBrush(QColor("#202730")); p.setPen(Qt.NoPen)
    p.drawRect(QRectF(c - 0.11 * s, 0.30 * s, 0.22 * s, 0.36 * s))
    p.setBrush(QColor("#e0b64f"))
    for xx in (c - 0.07 * s, c, c + 0.07 * s):
        p.drawRect(QRectF(xx - 0.012 * s, 0.58 * s, 0.024 * s, 0.06 * s))


def draw_antenna(p, theme, s):
    c = s / 2
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.42 * s)
    _lead(p, path, theme.sockets.get(1, theme.via), max(2.0, 0.13 * s))
    p.setBrush(Qt.NoBrush); p.setPen(_pen(QColor("#9fb4c8"), 1.4))
    for r in (0.10 * s, 0.17 * s, 0.24 * s):
        p.drawArc(QRectF(c - r, 0.42 * s - r, 2 * r, 2 * r), 30 * 16, 120 * 16)


def draw_battery(p, e0, theme, s):
    c = s / 2
    col = theme.sockets.get(e0, QColor("#e2503c"))
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.40 * s)
    _lead(p, path, col, max(2.0, 0.13 * s))
    p.setBrush(QColor("#25324a")); p.setPen(_pen(QColor("#c8d2dc"), 1.2))
    p.drawRoundedRect(QRectF(c - 0.11 * s, 0.40 * s, 0.22 * s, 0.34 * s), 0.03 * s, 0.03 * s)
    p.fillRect(QRectF(c - 0.045 * s, 0.35 * s, 0.09 * s, 0.05 * s), QColor("#c8d2dc"))
    p.fillRect(QRectF(c - 0.11 * s, 0.55 * s, 0.05 * s, 0.10 * s), QColor("#e2503c"))


def draw_mount(p, theme, s):
    c = QPointF(s / 2, s / 2)
    p.setBrush(QColor(theme.pad)); p.setPen(_pen(QColor(theme.pad).darker(160), 1.0))
    p.drawEllipse(c, 0.30 * s, 0.30 * s)
    p.setBrush(theme.bg); p.setPen(Qt.NoPen)
    p.drawEllipse(c, 0.13 * s, 0.13 * s)


def draw_fiducial(p, theme, s):
    c = QPointF(s / 2, s / 2)
    p.setBrush(Qt.NoBrush); p.setPen(_pen(QColor(226, 232, 238, 160), 1.0))
    p.drawEllipse(c, 0.16 * s, 0.16 * s)
    p.setBrush(QColor(theme.pad)); p.setPen(Qt.NoPen)
    p.drawEllipse(c, 0.07 * s, 0.07 * s)


def draw_silk(p, theme, s):
    c = QPointF(s / 2, s / 2)
    p.setBrush(Qt.NoBrush)
    p.setPen(_pen(QColor(226, 232, 238, 150), 1.1))
    p.drawRect(QRectF(c.x() - 0.20 * s, c.y() - 0.13 * s, 0.40 * s, 0.26 * s))
    f = QFont()
    f.setPixelSize(max(5, int(0.14 * s)))
    f.setBold(True)
    p.setFont(f)
    p.setPen(QPen(QColor(226, 232, 238, 200)))
    p.drawText(QRectF(0, 0, s, s), Qt.AlignCenter, "U1")


def draw_source(p, e0, theme, s):
    c = s / 2
    col = theme.sockets.get(e0, QColor("#e2503c"))
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.31 * s)
    _lead(p, path, col, max(2.0, 0.13 * s))
    body = QColor("#e2503c")
    p.setBrush(body); p.setPen(_pen(body.darker(150), 1.2))
    p.drawEllipse(QPointF(c, 0.50 * s), 0.19 * s, 0.19 * s)
    p.setPen(_pen(QColor("#f4f6f8"), max(1.4, 0.045 * s)))
    p.drawLine(QPointF(c - 0.09 * s, 0.50 * s), QPointF(c + 0.09 * s, 0.50 * s))
    p.drawLine(QPointF(c, 0.41 * s), QPointF(c, 0.59 * s))


def draw_gndsym(p, e0, theme, s):
    c = s / 2
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.52 * s)
    _lead(p, path, theme.sockets.get(e0, theme.via), max(2.0, 0.13 * s))
    bars = theme.sockets.get(3, theme.gate_edge)
    for wid, yy in ((0.36, 0.54), (0.24, 0.62), (0.12, 0.70)):
        p.fillRect(QRectF(c - wid * s / 2, yy * s, wid * s, 0.05 * s), bars)


def draw_led(p, theme, s):
    c = s / 2
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.36 * s)
    _lead(p, path, theme.sockets.get(1, theme.via), max(2.0, 0.13 * s))
    p.setBrush(QColor(226, 80, 60, 60)); p.setPen(Qt.NoPen)
    p.drawEllipse(QPointF(c, 0.52 * s), 0.27 * s, 0.27 * s)
    tri = QPainterPath(QPointF(c - 0.11 * s, 0.38 * s))
    tri.lineTo(QPointF(c + 0.11 * s, 0.38 * s))
    tri.lineTo(QPointF(c, 0.55 * s))
    tri.closeSubpath()
    p.setBrush(QColor("#e2503c")); p.setPen(_pen(QColor("#7a2a1e"), 1.0))
    p.drawPath(tri)
    p.setPen(_pen(QColor("#e2503c"), max(1.6, 0.05 * s)))
    p.drawLine(QPointF(c - 0.11 * s, 0.57 * s), QPointF(c + 0.11 * s, 0.57 * s))


def draw_switch(p, theme, s):
    c = s / 2
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.30 * s)
    _lead(p, path, theme.sockets.get(1, theme.via), max(2.0, 0.13 * s))
    p.setPen(_pen(theme.gate_edge, max(1.6, 0.05 * s)))
    p.drawLine(QPointF(c, 0.30 * s), QPointF(c + 0.16 * s, 0.64 * s))
    p.setBrush(QColor(theme.pad)); p.setPen(_pen(QColor(theme.pad).darker(160), 1.0))
    for yy in (0.30, 0.72):
        p.drawEllipse(QPointF(c, yy * s), 0.05 * s, 0.05 * s)


def draw_clocksrc(p, e0, theme, s):
    c = s / 2
    col = theme.sockets.get(e0, QColor("#38b6e3"))
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.31 * s)
    _lead(p, path, col, max(2.0, 0.13 * s))
    body = QColor("#38b6e3")
    p.setBrush(body); p.setPen(_pen(body.darker(150), 1.2))
    p.drawEllipse(QPointF(c, 0.50 * s), 0.19 * s, 0.19 * s)
    p.setPen(_pen(QColor("#08222e"), max(1.3, 0.04 * s)))
    x0, y0 = c - 0.09 * s, 0.50 * s
    sq = QPainterPath(QPointF(x0, y0 + 0.05 * s))
    for xx, yy in ((0.035, 0.05), (0.035, -0.05), (0.085, -0.05), (0.085, 0.05),
                   (0.135, 0.05), (0.135, -0.05), (0.18, -0.05)):
        sq.lineTo(x0 + xx * s, y0 + yy * s)
    p.drawPath(sq)


def draw_xtal(p, e0, theme, s):
    c = s / 2
    col = theme.sockets.get(e0, theme.sockets.get(2, theme.via))
    path = QPainterPath(QPointF(c, 0)); path.lineTo(c, 0.34 * s)
    _lead(p, path, col, max(2.0, 0.13 * s))
    p.setBrush(QColor("#b9c4cc")); p.setPen(_pen(QColor("#6d7a85"), 1.2))
    p.drawRoundedRect(QRectF(c - 0.11 * s, 0.34 * s, 0.22 * s, 0.30 * s), 0.08 * s, 0.08 * s)
    p.setBrush(QColor(theme.pad)); p.setPen(_pen(QColor(theme.pad).darker(160), 1.0))
    p.drawEllipse(QPointF(c, 0.78 * s), 0.04 * s, 0.04 * s)


def draw_fp_sub(p, tile, theme, s):
    info = FP_INFO[tile.base]
    w, h = fp_dims(tile.base, tile.rot)
    cx, cy = fp_cell(tile.kind)
    body = QColor(info["color"])
    edge = QColor(info["edge"])
    m = 0.10 * s
    x0 = m if cx == 0 else 0.0
    y0 = m if cy == 0 else 0.0
    x1 = s - m if cx == w - 1 else float(s)
    y1 = s - m if cy == h - 1 else float(s)
    mids = (QPointF(s / 2, 0), QPointF(s, s / 2), QPointF(s / 2, s), QPointF(0, s / 2))
    bod = (QPointF(s / 2, y0), QPointF(x1, s / 2), QPointF(s / 2, y1), QPointF(x0, s / 2))
    lw = max(1.6, 0.11 * s)
    for d in range(4):
        sk = tile.edges[d]
        if sk in (1, 2, 3):
            col = theme.sockets.get(sk, theme.via)
            path = QPainterPath(mids[d]); path.lineTo(bod[d])
            _lead(p, path, col, lw)
            p.setBrush(QColor(theme.pad)); p.setPen(_pen(QColor(theme.pad).darker(160), 1.0))
            p.drawEllipse(mids[d], 0.055 * s, 0.055 * s)
    p.setPen(Qt.NoPen); p.setBrush(body)
    p.drawRect(QRectF(x0, y0, x1 - x0, y1 - y0))
    p.setBrush(Qt.NoBrush); p.setPen(_pen(edge, 1.1))
    if cx == 0:
        p.drawLine(QPointF(x0, y0), QPointF(x0, y1))
    if cx == w - 1:
        p.drawLine(QPointF(x1, y0), QPointF(x1, y1))
    if cy == 0:
        p.drawLine(QPointF(x0, y0), QPointF(x1, y0))
    if cy == h - 1:
        p.drawLine(QPointF(x0, y1), QPointF(x1, y1))
    if (cx, cy) == (0, 0):
        p.setBrush(QColor(theme.pad)); p.setPen(Qt.NoPen)
        p.drawEllipse(QPointF(x0 + 0.17 * s, y0 + 0.17 * s), 0.045 * s, 0.045 * s)
    if (cx, cy) == fp_label_cell(tile.base, tile.rot):
        f = QFont(); f.setPixelSize(max(7, int(0.20 * s))); f.setBold(True)
        p.setFont(f); p.setPen(QPen(QColor("#e8eef4")))
        p.drawText(QRectF(0, 0, s, s), Qt.AlignCenter, info["label"])


def draw_gate(p, kind, rot, edges, theme, s):
    label, bubble, out_base, shape = GATE_STYLE[kind]
    o = (out_base + rot) % 4
    c = QPointF(s / 2, s / 2)
    mids = (QPointF(s / 2, 0), QPointF(s, s / 2), QPointF(s / 2, s), QPointF(0, s / 2))
    lw = max(2.0, 0.13 * s)
    for d in range(4):
        if edges[d]:
            path = QPainterPath(mids[d]); path.lineTo(c)
            _lead(p, path, theme.sockets.get(edges[d], theme.via), lw)
    half = 0.25 * s
    if shape == "seg":
        p.setBrush(QColor(255, 90, 74, 45)); p.setPen(Qt.NoPen)
        p.drawEllipse(c, 0.30 * s, 0.30 * s)
    p.setBrush(theme.gate_fill)
    p.setPen(_pen(theme.gate_edge, max(1.4, 0.045 * s)))
    if shape == "trap":
        path = QPainterPath(QPointF(0.27 * s, 0.20 * s))
        path.lineTo(QPointF(0.73 * s, 0.33 * s))
        path.lineTo(QPointF(0.73 * s, 0.67 * s))
        path.lineTo(QPointF(0.27 * s, 0.80 * s))
        path.closeSubpath()
        p.drawPath(path)
    else:
        p.drawRoundedRect(QRectF(c.x() - half, c.y() - half, 2 * half, 2 * half), 0.07 * s, 0.07 * s)
    vec = OUTV[o]
    f = QFont()
    f.setPixelSize(max(6, int((0.27 if len(label) <= 2 else 0.20) * s)))
    f.setBold(True)
    p.setFont(f)
    p.setPen(QPen(QColor("#ff6a55") if shape == "seg" else theme.gate_edge))
    lrect = QRectF(0, 0, s, s)
    lrect.translate(-vec.x() * 0.07 * s, -vec.y() * 0.07 * s)
    p.drawText(lrect, Qt.AlignCenter, label)
    if bubble:
        bp = c + vec * 0.32 * s
        p.setBrush(QColor(theme.bg))
        p.setPen(_pen(theme.gate_edge, max(1.2, 0.04 * s)))
        p.drawEllipse(bp, 0.08 * s, 0.08 * s)


def paint_tile(p, tile, s, theme):
    kind = tile.kind
    if kind == "blank":
        return
    if kind.startswith("fp_"):
        draw_fp_sub(p, tile, theme, s)
        return
    if kind.startswith("gate_"):
        draw_gate(p, kind, tile.rot, tile.edges, theme, s)
        return
    p.save()
    p.translate(s / 2, s / 2)
    p.rotate(tile.rot * 90)
    p.translate(-s / 2, -s / 2)
    be = tile.base_edges
    if kind == "trace":
        draw_trace(p, be, theme, s)
    elif kind == "via":
        draw_via(p, theme, s)
    elif kind == "resistor":
        draw_resistor(p, theme, s)
    elif kind == "cap":
        draw_cap(p, theme, s)
    elif kind == "elyt":
        draw_elyt(p, theme, s)
    elif kind == "inductor":
        draw_inductor(p, theme, s)
    elif kind == "diode":
        draw_diode(p, theme, s)
    elif kind == "pcb_led":
        draw_pcb_led(p, theme, s)
    elif kind == "crystal":
        draw_crystal(p, theme, s)
    elif kind == "ferrite":
        draw_ferrite(p, theme, s)
    elif kind == "fuse":
        draw_fuse(p, theme, s)
    elif kind == "transformer":
        draw_transformer(p, theme, s)
    elif kind == "header":
        draw_header(p, theme, s)
    elif kind == "chip":
        draw_chip(p, theme, s)
    elif kind == "qfp":
        draw_trace(p, be, theme, s); draw_qfp(p, theme, s)
    elif kind == "opamp":
        draw_trace(p, be, theme, s); draw_opamp(p, theme, s)
    elif kind == "regulator":
        draw_regulator(p, be, theme, s)
    elif kind == "transistor":
        draw_transistor(p, theme, s)
    elif kind == "testpoint":
        draw_testpoint(p, theme, s)
    elif kind == "button":
        draw_button(p, theme, s)
    elif kind == "pot":
        draw_pot(p, theme, s)
    elif kind == "piezo":
        draw_piezo(p, theme, s)
    elif kind == "speaker":
        draw_speaker(p, theme, s)
    elif kind == "motor":
        draw_motor(p, theme, s)
    elif kind == "usb":
        draw_usb(p, theme, s)
    elif kind == "antenna":
        draw_antenna(p, theme, s)
    elif kind == "battery":
        draw_battery(p, be[0], theme, s)
    elif kind == "mount":
        draw_mount(p, theme, s)
    elif kind == "fiducial":
        draw_fiducial(p, theme, s)
    elif kind == "silk":
        draw_silk(p, theme, s)
    elif kind == "source":
        draw_source(p, be[0], theme, s)
    elif kind == "gndsym":
        draw_gndsym(p, be[0], theme, s)
    elif kind == "led":
        draw_led(p, theme, s)
    elif kind == "switch":
        draw_switch(p, theme, s)
    elif kind == "clocksrc":
        draw_clocksrc(p, be[0], theme, s)
    elif kind == "xtal":
        draw_xtal(p, be[0], theme, s)
    p.restore()


# --------------------------------------------------------------------------- WFC core

class Contradiction(Exception):
    pass


def build_prop_tables(tiles):
    maxs = 3
    for t in tiles:
        maxs = max(maxs, max(t.edges))
    by = [[0] * (maxs + 1) for _ in range(4)]
    for j, t in enumerate(tiles):
        b = 1 << j
        for d in range(4):
            by[d][t.edges[d]] |= b
    sock_ids = [s for s in range(maxs + 1) if any(by[d][s] for d in range(4))]
    any_out = []
    for d in range(4):
        m = 0
        for s in range(1, maxs + 1):
            m |= by[d][s]
        any_out.append(m)
    return by, sock_ids, any_out


class WFCModel:
    """Bitmask superpositions, heap-ordered min-entropy collapse, stack propagation.
    Supports per-cell weight multipliers (zones) via self.cw."""

    def __init__(self, w, h, tiles, weights, rng, prop):
        self.w, self.h, self.n = w, h, w * h
        self.T = len(tiles)
        self.rng = rng
        self.weights = list(weights)
        self.logw = [math.log(max(x, 1e-9)) for x in weights]
        self.by, self.sock_ids, self.any_out = prop
        self.cw = {}                      # cell -> (weights, logw) for zones
        full = (1 << self.T) - 1
        self.mask = [full] * self.n
        self.count = [self.T] * self.n
        sw = sum(weights)
        swl = sum(x * math.log(max(x, 1e-9)) for x in weights)
        self.sumw = [sw] * self.n
        self.sumwlog = [swl] * self.n
        self.noise = [rng.random() * 1e-4 for _ in range(self.n)]
        self.collapsed = [False] * self.n
        self.tile_of = [-1] * self.n
        self.heap = []
        self.rebuild_heap()

    def _wf(self, i):
        c = self.cw.get(i)
        return c if c is not None else (self.weights, self.logw)

    def set_zone_weights(self, multmap):
        """multmap: {cell: [per-tile multipliers]} or None to clear."""
        if multmap:
            cw = {}
            for i, mults in multmap.items():
                wl = [self.weights[t] * mults[t] for t in range(self.T)]
                lw = [math.log(max(x, 1e-9)) for x in wl]
                cw[i] = (wl, lw)
            self.cw = cw
            for i in cw:
                if not self.collapsed[i]:
                    self._resum(i)
        else:
            self.cw = {}
            for i in range(self.n):
                if not self.collapsed[i]:
                    self._resum(i)

    def _resum(self, i):
        self._recount(i, self.mask[i])
        self._push(i)

    def entropy(self, i):
        s = self.sumw[i]
        return math.log(max(s, 1e-9)) - self.sumwlog[i] / max(s, 1e-9) + self.noise[i]

    def rebuild_heap(self):
        self.heap = [(self.entropy(i), i) for i in range(self.n) if not self.collapsed[i]]
        heapq.heapify(self.heap)

    def _push(self, i):
        if not self.collapsed[i]:
            heapq.heappush(self.heap, (self.entropy(i), i))

    def _pop(self):
        heap = self.heap
        while heap:
            e, i = heap[0]
            if self.collapsed[i]:
                heapq.heappop(heap)
                continue
            cur = self.entropy(i)
            if cur != e:
                heapq.heapreplace(heap, (cur, i))
                continue
            heapq.heappop(heap)
            return i
        return -1

    def snapshot(self):
        return (self.mask[:], self.count[:], self.sumw[:], self.sumwlog[:],
                self.collapsed[:], self.tile_of[:], self.heap[:], self.cw)

    def restore(self, snap):
        (self.mask, self.count, self.sumw, self.sumwlog,
         self.collapsed, self.tile_of, self.heap, self.cw) = (snap[0][:], snap[1][:],
                                                              snap[2][:], snap[3][:],
                                                              snap[4][:], snap[5][:],
                                                              snap[6][:], snap[7])

    def _recount(self, i, mask):
        w, logw = self._wf(i)
        c, sw_, swl_ = 0, 0.0, 0.0
        mm = mask
        while mm:
            b = mm & -mm
            t = b.bit_length() - 1
            mm ^= b
            c += 1
            sw_ += w[t]
            swl_ += logw[t] * w[t]
        self.mask[i] = mask
        self.count[i] = c
        self.sumw[i] = sw_
        self.sumwlog[i] = swl_
        if c <= 0:
            raise Contradiction(f"cell {i}")

    def apply_border(self):
        full = (1 << self.T) - 1
        no_out = [full & ~m for m in self.any_out]
        seeds = []
        for y in range(self.h):
            for x in range(self.w):
                mask = full
                if y == 0:
                    mask &= no_out[N]
                if x == self.w - 1:
                    mask &= no_out[E]
                if y == self.h - 1:
                    mask &= no_out[S]
                if x == 0:
                    mask &= no_out[W]
                if mask != full:
                    i = y * self.w + x
                    self._recount(i, mask)
                    seeds.append(i)
        if seeds:
            self.propagate(seeds)

    def _pick(self, i):
        w, _ = self._wf(i)
        target = self.rng.random() * max(self.sumw[i], 1e-9)
        m, acc, chosen = self.mask[i], 0.0, None
        while m:
            b = m & -m
            t = b.bit_length() - 1
            m ^= b
            acc += w[t]
            if target < acc:
                chosen = t
                break
        if chosen is None:
            m = self.mask[i]
            chosen = (m & -m).bit_length() - 1
        return chosen

    def collapse(self, i, t=None):
        t = self._pick(i) if t is None else t
        w, logw = self._wf(i)
        wt = w[t]
        self.mask[i] = 1 << t
        self.count[i] = 1
        self.sumw[i] = wt
        self.sumwlog[i] = logw[t] * wt
        self.collapsed[i] = True
        self.tile_of[i] = t
        return (i,)

    def collapse_to(self, i, t):
        self.collapse(i, t)
        self.propagate((i,))

    def close_forced(self):
        while self.heap:
            e, i = self.heap[0]
            if self.collapsed[i]:
                heapq.heappop(self.heap)
                continue
            cur = self.entropy(i)
            if cur != e:
                heapq.heapreplace(self.heap, (cur, i))
                continue
            if self.count[i] != 1:
                return
            heapq.heappop(self.heap)
            t = (self.mask[i] & -self.mask[i]).bit_length() - 1
            self.collapse(i, t)
            self.propagate((i,))

    def propagate(self, seeds):
        stack = list(seeds)
        masks = self.mask
        by = self.by
        sock_ids = self.sock_ids
        while stack:
            i = stack.pop()
            x, y = i % self.w, i // self.w
            mi = masks[i]
            for d in range(4):
                nx, ny = x + DIRS[d][0], y + DIRS[d][1]
                if nx < 0 or ny < 0 or nx >= self.w or ny >= self.h:
                    continue
                j = ny * self.w + nx
                sup = 0
                frow, brow = by[d], by[OPP[d]]
                for s in sock_ids:
                    if mi & frow[s]:
                        sup |= brow[s]
                new = masks[j] & sup
                if new != masks[j]:
                    self._recount(j, new)
                    self._push(j)
                    stack.append(j)

    def step(self):
        i = self._pop()
        if i < 0:
            return None
        self.collapse(i)
        self.propagate((i,))
        return i

    def is_done(self):
        return all(self.collapsed)

    def fill_remaining(self):
        for i in range(self.n):
            if not self.collapsed[i]:
                t = self._pick(i)
                w, logw = self._wf(i)
                wt = w[t]
                self.mask[i] = 1 << t
                self.count[i] = 1
                self.sumw[i] = wt
                self.sumwlog[i] = logw[t] * wt
                self.collapsed[i] = True
                self.tile_of[i] = t


# --------------------------------------------------------------------------- MCTS solver

class MCTSNode:
    __slots__ = ("parent", "move", "children", "untried", "visits", "score",
                 "terminal", "cell")

    def __init__(self, parent, move):
        self.parent = parent
        self.move = move
        self.children = []
        self.untried = None
        self.visits = 0
        self.score = 0.0
        self.terminal = None
        self.cell = None


class MCTSSolver:
    def __init__(self, pristine, c=1.4):
        self.pristine = pristine
        self.c = c
        self.root = MCTSNode(None, None)
        self.nodes = 1
        self.iters = 0
        self.best_snap = None
        self.best_done = 0
        self.solved_snap = None

    def _uct(self, node, parent_n):
        if node.visits == 0:
            return float("inf")
        return (node.score / node.visits
                + self.c * math.sqrt(math.log(parent_n + 1) / node.visits))

    def _note_progress(self, m):
        c = sum(m.collapsed)
        if c > self.best_done:
            self.best_done = c
            self.best_snap = m.snapshot()
            if c == m.n:
                self.solved_snap = self.best_snap

    @staticmethod
    def _mask_tiles(m, cell):
        out = []
        mask = m.mask[cell]
        while mask:
            b = mask & -mask
            out.append(b.bit_length() - 1)
            mask ^= b
        return out

    @staticmethod
    def _weighted_pick(m, cell, tiles):
        w, _ = m._wf(cell)
        tot = sum(w[t] for t in tiles)
        if tot <= 0:
            return tiles[m.rng.randrange(len(tiles))]
        x = m.rng.random() * tot
        acc = 0.0
        for t in tiles:
            acc += w[t]
            if x < acc:
                return t
        return tiles[-1]

    def iterate(self, m):
        m.restore(self.pristine)
        self.iters += 1
        node = self.root
        try:
            while node.terminal is None and node.untried == [] and node.children:
                node = max(node.children, key=lambda ch: self._uct(ch, node.visits))
                m.collapse_to(node.move[0], node.move[1])
                m.close_forced()
        except Contradiction:
            node.terminal = "loss"

        if node.terminal == "win":
            r = 1.0
        elif node.terminal == "loss":
            r = 0.0
        else:
            cell = m._pop()
            if cell < 0:
                node.terminal = "win"
                self._note_progress(m)
                r = 1.0
            else:
                if node.untried is None:
                    node.cell = cell
                    node.untried = self._mask_tiles(m, cell)
                if node.untried:
                    t = self._weighted_pick(m, node.cell, node.untried)
                    node.untried.remove(t)
                    child = MCTSNode(node, (node.cell, t))
                    node.children.append(child)
                    self.nodes += 1
                    node = child
                    try:
                        m.collapse_to(node.cell, t)
                        m.close_forced()
                    except Contradiction:
                        node.terminal = "loss"
                        r = 0.0
                    else:
                        if m.is_done():
                            node.terminal = "win"
                            self._note_progress(m)
                            r = 1.0
                        else:
                            self._note_progress(m)
                            r = self._rollout(m)
                else:
                    node.terminal = "loss"
                    r = 0.0

        while node is not None:
            node.visits += 1
            node.score += r
            node = node.parent

    def _rollout(self, m):
        n = m.n
        for _ in range(n + 4):
            cell = m._pop()
            if cell < 0:
                if all(m.collapsed):
                    self._note_progress(m)
                    return 1.0
                break
            t = self._weighted_pick(m, cell, self._mask_tiles(m, cell))
            try:
                m.collapse_to(cell, t)
                m.close_forced()
            except Contradiction:
                return 0.0
        return 0.25 * sum(m.collapsed) / n


# --------------------------------------------------------------------------- autorouter

def find_open_ends(model, tiles, gw, gh):
    """Sockets that face off-board or a mismatched neighbour."""
    ends = []
    for i in range(model.n):
        t = tiles[model.tile_of[i]]
        x, y = i % gw, i // gw
        for d in range(4):
            s = t.edges[d]
            if not s:
                continue
            nx, ny = x + DIRS[d][0], y + DIRS[d][1]
            if not (0 <= nx < gw and 0 <= ny < gh):
                ends.append((i, d, s, True))
                continue
            j = ny * gw + nx
            if tiles[model.tile_of[j]].edges[OPP[d]] != s:
                ends.append((i, d, s, False))
    return ends


def _passable(model, tiles, i, s):
    for e in tiles[model.tile_of[i]].edges:
        if e != 0 and e != s:
            return False
    return True


def _tile_with_edges(tiles, edges):
    best, bw = None, -1.0
    for ti, t in enumerate(tiles):
        if t.edges == edges and t.weight > bw:
            best, bw = ti, t.weight
    return best


def _dir_between(a, b, gw):
    dx, dy = b % gw - a % gw, b // gw - a // gw
    for d in range(4):
        if DIRS[d] == (dx, dy):
            return d
    return 0


def _manh_min(c, goals, gw):
    x, y = c % gw, c // gw
    return min(abs(x - g % gw) + abs(y - g // gw) for g in goals)


def _astar_path(model, tiles, gw, gh, s, starts, goals):
    if not starts or not goals:
        return None
    common = set(starts) & set(goals)
    if common:
        return [common.pop()]
    passable = bytearray(model.n)
    for i in range(model.n):
        if _passable(model, tiles, i, s):
            passable[i] = 1
    for c in list(starts) + list(goals):
        passable[c] = 1
    gscore, prev = {}, {}
    pq = []
    goalset = set(goals)
    for st in starts:
        gscore[st] = 0
        heapq.heappush(pq, (_manh_min(st, goals, gw), 0.0, st))
    expansions, limit = 0, 8 * model.n
    while pq and expansions < limit:
        f, g, c = heapq.heappop(pq)
        if g > gscore.get(c, 1e18):
            continue
        if c in goalset:
            path = [c]
            while c in prev:
                c = prev[c]
                path.append(c)
            path.reverse()
            return path
        expansions += 1
        x, y = c % gw, c // gw
        for d in range(4):
            nx, ny = x + DIRS[d][0], y + DIRS[d][1]
            if not (0 <= nx < gw and 0 <= ny < gh):
                continue
            n = ny * gw + nx
            if not passable[n]:
                continue
            step = 1.0
            if (tiles[model.tile_of[c]].edges[d] == s
                    and tiles[model.tile_of[n]].edges[OPP[d]] == s):
                step = 0.3
            ng = g + step
            if ng < gscore.get(n, 1e18):
                gscore[n] = ng
                prev[n] = c
                heapq.heappush(pq, (ng + _manh_min(n, goals, gw), ng, n))
    return None


def autoroute_stubs(model, tiles, gw, gh, max_routes=48):
    """Pair open ends of the same socket and carve trace paths between them
    (Lee/A* through blank and same-socket cells). Returns repaired count."""
    ends = find_open_ends(model, tiles, gw, gh)
    if not ends:
        return 0
    repaired = 0

    def neighbor(i, d):
        x, y = i % gw, i // gw
        nx, ny = x + DIRS[d][0], y + DIRS[d][1]
        if 0 <= nx < gw and 0 <= ny < gh:
            return ny * gw + nx
        return None

    def assign(i, ti):
        w = model.weights[ti]
        model.mask[i] = 1 << ti
        model.count[i] = 1
        model.sumw[i] = w
        model.sumwlog[i] = model.logw[ti] * w
        model.collapsed[i] = True
        model.tile_of[i] = ti

    def carve_plan(i, conns, drop_dir, s):
        t0 = tiles[model.tile_of[i]]
        edges = []
        for d in range(4):
            cur = t0.edges[d]
            if d == drop_dir:
                edges.append(0)
            elif d in conns:
                if cur not in (0, s):
                    return None
                edges.append(s)
            elif cur in (0, s):
                edges.append(cur)
            else:
                return None
        tt = tuple(edges)
        if tt == t0.edges:
            return model.tile_of[i]
        return _tile_with_edges(tiles, tt)

    def try_route(e1, e2, s):
        i1, d1, _, b1 = e1
        i2, d2, _, b2 = e2
        drop1 = d1 if b1 else None
        drop2 = d2 if b2 else None
        if b1:
            starts = [neighbor(i1, d) for d in range(4)
                      if d != d1 and neighbor(i1, d) is not None
                      and _passable(model, tiles, neighbor(i1, d), s)]
        else:
            n1 = neighbor(i1, d1)
            starts = [n1] if n1 is not None and _passable(model, tiles, n1, s) else []
        if b2:
            goals = [neighbor(i2, d) for d in range(4)
                     if d != d2 and neighbor(i2, d) is not None
                     and _passable(model, tiles, neighbor(i2, d), s)]
        else:
            n2 = neighbor(i2, d2)
            goals = [n2] if n2 is not None and _passable(model, tiles, n2, s) else []
        path = _astar_path(model, tiles, gw, gh, s, starts, goals)
        if path is None:
            return False
        chain = [i1] + path + [i2]
        plans = []
        for k, c in enumerate(chain):
            conns = set()
            if k > 0:
                conns.add(_dir_between(chain[k - 1], c, gw))
            if k < len(chain) - 1:
                conns.add(_dir_between(c, chain[k + 1], gw))
            if k == 0 and not b1:
                conns.add(d1)
            if k == len(chain) - 1 and not b2:
                conns.add(d2)
            dr = drop1 if k == 0 else (drop2 if k == len(chain) - 1 else None)
            ti = carve_plan(c, conns, dr, s)
            if ti is None:
                return False
            plans.append((c, ti))
        for c, ti in plans:
            assign(c, ti)
        return True

    def drop_socket(e):
        i, d, s, _b = e
        t0 = tiles[model.tile_of[i]]
        edges = list(t0.edges)
        edges[d] = 0
        ti = _tile_with_edges(tiles, tuple(edges))
        if ti is None:
            return False
        assign(i, ti)
        return True

    by_sock = defaultdict(list)
    for e in ends:
        by_sock[e[2]].append(e)
    leftovers = []
    for s, lst in by_sock.items():
        guard = 0
        while len(lst) >= 2 and repaired < max_routes and guard < 200:
            guard += 1
            e1 = lst.pop(0)
            lst.sort(key=lambda e: abs(e[0] % gw - e1[0] % gw)
                     + abs(e[0] // gw - e1[0] // gw))
            placed = False
            for e2 in lst[:3]:
                if try_route(e1, e2, s):
                    lst.remove(e2)
                    repaired += 1
                    placed = True
                    break
            if not placed:
                leftovers.append(e1)
        leftovers.extend(lst)
    for e in leftovers:
        if e[3] and repaired < max_routes:
            if drop_socket(e):
                repaired += 1
    return repaired


# --------------------------------------------------------------------------- netlist extraction

@dataclass
class Net:
    name: str
    sock: int
    cells: set
    kinds: set
    driven: bool
    comps: int = 0
    internal: bool = False


def extract_net_groups(model, tiles, gw, gh):
    parent = {}

    def find(a):
        r = a
        while parent[r] != r:
            r = parent[r]
        while parent[a] != r:
            parent[a], a = r, parent[a]
        return r

    def add(k):
        if k not in parent:
            parent[k] = k

    for i in range(model.n):
        td = tiles[model.tile_of[i]].edges
        x, y = i % gw, i // gw
        for d in range(4):
            s = td[d]
            if not s:
                continue
            add((i, s))
            nx, ny = x + DIRS[d][0], y + DIRS[d][1]
            if 0 <= nx < gw and 0 <= ny < gh:
                j = ny * gw + nx
                if tiles[model.tile_of[j]].edges[(d + 2) % 4] == s:
                    add((j, s))
                    ra, rb = find((i, s)), find((j, s))
                    if ra != rb:
                        parent[ra] = rb

    root_id = {}
    groups = []
    for k in parent:
        r = find(k)
        if r not in root_id:
            root_id[r] = len(groups)
            groups.append([set(), defaultdict(int), set()])
    node_net = {}
    for k in parent:
        i, s = k
        g = groups[root_id[find(k)]]
        g[0].add(i)
        g[1][s] += 1
        g[2].add(tiles[model.tile_of[i]].kind)
        node_net[k] = root_id[find(k)]
    out = []
    for cells, socks, kinds in groups:
        sock = max(socks, key=lambda q: socks[q])
        out.append((cells, sock, kinds))
    return out, node_net


# --------------------------------------------------------------------------- timeline view

class TLView:
    """Read-only collapsed/tile_of view over a recorded timeline frame."""
    __slots__ = ("collapsed", "tile_of", "n", "count", "mask", "T")

    def __init__(self, tl, n):
        self.tile_of = tl
        self.collapsed = [t >= 0 for t in tl]
        self.n = n
        self.count = [0] * n
        self.mask = [0] * n
        self.T = 1


# --------------------------------------------------------------------------- minimap

class Minimap(QWidget):
    def __init__(self, main, parent):
        super().__init__(parent)
        self.main = main
        self.setFixedSize(148, 148)
        self._drag = False
        self.cache = None
        self.cache_rev = -1
        self._last_build = 0.0

    def _geometry(self):
        main = self.main
        bw, bh = max(1, main.gw), max(1, main.gh)
        sc = min((self.width() - 8) / bw, (self.height() - 8) / bh)
        ox = (self.width() - bw * sc) / 2
        oy = (self.height() - bh * sc) / 2
        return sc, ox, oy

    def paintEvent(self, ev):
        main = self.main
        p = QPainter(self)
        p.fillRect(self.rect(), QColor("#0b0e13"))
        sc, ox, oy = self._geometry()
        layer = main.board.layer
        rev = main.board.layer_rev
        now = time.monotonic()
        if (self.cache is None or self.cache_rev != rev) and layer is not None \
                and now - self._last_build > 0.15:
            self.cache = layer.scaled(self.width() - 8, self.height() - 8,
                                      Qt.KeepAspectRatio, Qt.FastTransformation)
            self.cache_rev = rev
            self._last_build = now
        if self.cache is not None and not self.cache.isNull():
            cw, ch = self.cache.width(), self.cache.height()
            p.drawPixmap(int(ox + (main.gw * sc - cw) / 2), int(oy + (main.gh * sc - ch) / 2),
                         cw, ch, self.cache)
        else:
            p.fillRect(QRectF(ox, oy, main.gw * sc, main.gh * sc), main.theme.bg)
        vs = main.rscroll.verticalScrollBar()
        hs = main.rscroll.horizontalScrollBar()
        vp = main.rscroll.viewport()
        vx = hs.value() / max(1.0, main.cell)
        vy = vs.value() / max(1.0, main.cell)
        vw = vp.width() / max(1.0, main.cell)
        vh = vp.height() / max(1.0, main.cell)
        p.setPen(QPen(QColor(90, 162, 232), 2))
        p.setBrush(Qt.NoBrush)
        p.drawRect(QRectF(ox + vx * sc, oy + vy * sc, vw * sc, vh * sc))
        p.setPen(QPen(QColor("#2a313a"), 1))
        p.drawRect(self.rect().adjusted(0, 0, -1, -1))

    def _nav(self, pos):
        main = self.main
        sc, ox, oy = self._geometry()
        cx = (pos.x() - ox) / sc
        cy = (pos.y() - oy) / sc
        hs = main.rscroll.horizontalScrollBar()
        vs = main.rscroll.verticalScrollBar()
        vp = main.rscroll.viewport()
        hs.setValue(int(cx * main.cell - vp.width() / 2))
        vs.setValue(int(cy * main.cell - vp.height() / 2))

    def mousePressEvent(self, e):
        self._drag = True
        self._nav(e.position())

    def mouseMoveEvent(self, e):
        if self._drag:
            self._nav(e.position())

    def mouseReleaseEvent(self, e):
        self._drag = False


# --------------------------------------------------------------------------- board widget

class BoardWidget(QWidget):
    def __init__(self, main):
        super().__init__()
        self.main = main
        self.pixcache = {}
        self.layer = None
        self.layer_done = bytearray()
        self.layer_rev = 0
        self._painting = False
        self.setMouseTracking(True)

    def invalidate_layer(self):
        self.layer = None
        self.layer_rev += 1
        self.update()

    def ensure_layer(self, w, h, s):
        need = w * h
        if (self.layer is None or self.layer.width() != w * s
                or self.layer.height() != h * s or len(self.layer_done) != need):
            self.layer = QPixmap(w * s, h * s)
            self.layer.fill(Qt.transparent)
            self.layer_done = bytearray(need)

    def sync_layer(self, model, tiles, s, gw):
        pt = None
        changed = False
        for i in range(model.n):
            done = self.layer_done[i]
            if model.collapsed[i]:
                if not done:
                    if pt is None:
                        pt = QPainter(self.layer)
                        pt.setRenderHint(QPainter.Antialiasing)
                        pt.setRenderHint(QPainter.TextAntialiasing)
                    t = tiles[model.tile_of[i]]
                    if t.kind != "blank":
                        pt.drawPixmap((i % gw) * s, (i // gw) * s, self.tile_pixmap(t, s))
                    self.layer_done[i] = 1
                    changed = True
            elif done:
                if pt is None:
                    pt = QPainter(self.layer)
                pt.setCompositionMode(QPainter.CompositionMode_Clear)
                pt.fillRect((i % gw) * s, (i // gw) * s, s, s, Qt.transparent)
                pt.setCompositionMode(QPainter.CompositionMode_SourceOver)
                self.layer_done[i] = 0
                changed = True
        if pt is not None:
            pt.end()
        if changed:
            self.layer_rev += 1

    def tile_pixmap(self, t, size):
        key = (t.kind, t.rot, size)
        pm = self.pixcache.get(key)
        if pm is None:
            ss = 2
            pm = QPixmap(size * ss, size * ss)
            pm.fill(Qt.transparent)
            pt = QPainter(pm)
            pt.setRenderHint(QPainter.Antialiasing)
            pt.setRenderHint(QPainter.TextAntialiasing)
            pt.scale(ss, ss)
            paint_tile(pt, t, size, self.main.theme)
            pt.end()
            pm.setDevicePixelRatio(ss)
            self.pixcache[key] = pm
        return pm

    def paintEvent(self, ev):
        main = self.main
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        p.fillRect(self.rect(), main.theme.bg)
        view = main.paint_view()
        if view is None:
            return
        s, gw, gh = main.cell, main.gw, main.gh
        tl_mode = main.timeline_active()
        self.ensure_layer(gw, gh, s)
        self.sync_layer(view, main.tiles, s, gw)
        p.drawPixmap(0, 0, self.layer)

        if main.outline_check.isChecked():
            p.setPen(QPen(QColor(226, 232, 238, 90), 2))
            p.setBrush(Qt.NoBrush)
            p.drawRect(0, 0, gw * s - 1, gh * s - 1)

        ghosts = main.show_ghosts.isChecked() and not tl_mode
        active = main.active_sockets
        for i in range(view.n):
            if not view.collapsed[i]:
                x, y = (i % gw) * s, (i // gw) * s
                p.fillRect(x, y, s, s, main.theme.cell)
                cnt = view.count[i]
                if ghosts and 2 <= cnt <= 6:
                    m = view.mask[i]
                    p.setOpacity(min(0.85, 1.5 / cnt))
                    while m:
                        b = m & -m
                        tt = b.bit_length() - 1
                        m ^= b
                        t = main.tiles[tt]
                        if t.kind != "blank":
                            p.drawPixmap(x, y, self.tile_pixmap(t, s))
                    p.setOpacity(1.0)
                elif not tl_mode:
                    a = int(30 * (1.0 - cnt / view.T))
                    if a > 0:
                        p.fillRect(x, y, s, s, QColor(255, 255, 255, a))

        if main.sim_active() and not tl_mode:
            self.paint_sim(p, s, gw, view)
        if main.show_grid.isChecked():
            p.setPen(QPen(main.theme.grid, 1))
            for gx in range(gw + 1):
                p.drawLine(gx * s, 0, gx * s, gh * s)
            for gy in range(gh + 1):
                p.drawLine(0, gy * s, gw * s, gy * s)

        if main.zones:
            f = QFont()
            f.setPixelSize(max(9, s // 2))
            f.setBold(True)
            for (x0, y0, x1, y1, pname) in main.zones:
                zc = QColor(ZONE_COLORS.get(pname, "#9aa4ae"))
                fill = QColor(zc)
                fill.setAlpha(26)
                p.fillRect(x0 * s, y0 * s, (x1 - x0 + 1) * s, (y1 - y0 + 1) * s, fill)
                p.setBrush(Qt.NoBrush)
                p.setPen(QPen(zc, 2, Qt.DashLine))
                p.drawRect(x0 * s, y0 * s, (x1 - x0 + 1) * s - 1, (y1 - y0 + 1) * s - 1)
                p.setPen(QPen(zc))
                p.setFont(f)
                p.drawText(x0 * s + 4, y0 * s + 4 + f.pixelSize(), pname)
        if main.zone_drag is not None:
            x0, y0, x1, y1 = main.zone_drag
            p.setBrush(QColor(255, 255, 255, 24))
            p.setPen(QPen(QColor(255, 255, 255, 180), 2, Qt.DashLine))
            p.drawRect(min(x0, x1) * s, min(y0, y1) * s,
                       (abs(x1 - x0) + 1) * s - 1, (abs(y1 - y0) + 1) * s - 1)

        if main.nets and not tl_mode:
            if main.selected_net is not None:
                self.paint_net(p, s, gw, main.selected_net, 70)
            if main.hover_idx >= 0 and main.cell_nets.get(main.hover_idx):
                for nid in main.cell_nets[main.hover_idx]:
                    if nid != main.selected_net:
                        self.paint_net(p, s, gw, nid, 38)
        if main.fp_highlight:
            cells = main.fp_highlight
            xs = [i % gw for i in cells]
            ys = [i // gw for i in cells]
            for i in cells:
                p.fillRect((i % gw) * s, (i // gw) * s, s, s, QColor(255, 255, 255, 26))
            p.setBrush(Qt.NoBrush)
            p.setPen(QPen(QColor(245, 197, 66, 220), 2))
            p.drawRect(min(xs) * s, min(ys) * s,
                       (max(xs) - min(xs) + 1) * s - 1, (max(ys) - min(ys) + 1) * s - 1)
        if main.pins:
            p.setBrush(QColor("#f5c542")); p.setPen(_pen(QColor("#7a5c10"), 1.0))
            for idx in main.pins:
                x, y = (idx % gw) * s, (idx // gw) * s
                tri = QPainterPath(QPointF(x + 1, y + 1))
                tri.lineTo(QPointF(x + 0.4 * s, y + 1))
                tri.lineTo(QPointF(x + 1, y + 0.4 * s))
                tri.closeSubpath()
                p.drawPath(tri)
        if 0 <= main.hover_idx < view.n:
            x, y = (main.hover_idx % gw) * s, (main.hover_idx // gw) * s
            p.setBrush(Qt.NoBrush)
            p.setPen(QPen(QColor(90, 162, 232, 200), 2))
            p.drawRect(x + 1, y + 1, s - 2, s - 2)
        if (main.pin_mode_btn.isChecked() and main.pin_base in FP_INFO
                and 0 <= main.hover_idx < view.n):
            self.paint_fp_preview(p, s, gw, gh)
        if main.flashes:
            now = time.monotonic()
            for idx, t0 in main.flashes:
                k = max(0.0, 1.0 - (now - t0) / 0.4)
                if k > 0:
                    p.setOpacity(k * 0.7)
                    p.fillRect((idx % gw) * s, (idx // gw) * s, s, s, QColor(255, 255, 255))
            p.setOpacity(1.0)

    def paint_fp_preview(self, p, s, gw, gh):
        main = self.main
        base = main.pin_base
        rot = main.fp_rot
        anchor = main.hover_idx
        hx, hy = anchor % gw, anchor // gw
        w2, h2 = fp_dims(base, rot)
        m = main.model
        placed = 0
        total = w2 * h2
        p.setOpacity(0.55)
        for cy in range(h2):
            for cx in range(w2):
                bx, by = hx + cx, hy + cy
                if not (0 <= bx < gw and 0 <= by < gh):
                    continue
                ti = main.fp_var_cell.get((base, rot, cx, cy))
                if ti is None:
                    continue
                p.drawPixmap(bx * s, by * s, self.tile_pixmap(main.tiles[ti], s))
                placed += 1
        p.setOpacity(1.0)
        legal = False
        if placed == total and m is not None:
            vs = main.fp_anchor_variants.get((base, rot), ())
            legal = any((m.mask[anchor] >> ti) & 1 for ti in vs)
        col = QColor(80, 220, 120, 80) if legal else QColor(230, 80, 80, 80)
        ew, eh = min(w2, gw - hx), min(h2, gh - hy)
        if ew > 0 and eh > 0:
            p.setBrush(col)
            p.setPen(QPen(QColor(255, 255, 255, 150), 2))
            p.drawRect(hx * s, hy * s, ew * s - 1, eh * s - 1)

    def paint_net(self, p, s, gw, nid, alpha):
        main = self.main
        net = main.nets[nid]
        col = QColor(main.theme.sockets.get(net.sock, main.theme.via))
        col.setAlpha(alpha)
        for i in net.cells:
            p.fillRect((i % gw) * s, (i // gw) * s, s, s, col)
        if alpha > 50:
            edge = QColor(main.theme.sockets.get(net.sock, main.theme.via))
            edge.setAlpha(220)
            p.setPen(QPen(edge, 2))
            p.setBrush(Qt.NoBrush)
            for i in net.cells:
                p.drawRect((i % gw) * s + 1, (i // gw) * s + 1, s - 2, s - 2)

    def paint_sim(self, p, s, gw, model):
        main = self.main
        bus = main.theme.bus_socket
        dist = main.sim_dist
        tick = main.sim_tick
        for i in range(model.n):
            if not model.collapsed[i]:
                continue
            t = main.tiles[model.tile_of[i]]
            k = t.kind
            x, y = (i % gw) * s, (i // gw) * s
            if bus and bus in t.edges and (i + tick // 2) % 8 < 4:
                p.fillRect(x, y, s, s, QColor(176, 122, 224, 34))
            if k in ("led", "pcb_led"):
                if main.sim_vals[i]:
                    p.setBrush(QColor(255, 96, 74, 140)); p.setPen(Qt.NoPen)
                    p.drawEllipse(QPointF(x + s / 2, y + s / 2), 0.46 * s, 0.46 * s)
            elif k == "switch":
                if main._sw(i):
                    p.fillRect(x, y, s, s, QColor(255, 215, 90, 60))
            elif main.sim_vals[i]:
                sock = next((e for e in t.edges if e in (1, 2, 3)), 1)
                cc = main.theme.sockets.get(sock, main.theme.via)
                p.fillRect(x, y, s, s, QColor(cc.red(), cc.green(), cc.blue(), 46))
                if dist and i < len(dist) and dist[i] < 10 ** 6 and (tick - dist[i]) % 14 < 2:
                    p.fillRect(x, y, s, s, QColor(cc.red(), cc.green(), cc.blue(), 110))
            elif k in ("gate_ram", "gate_rom", "gate_seg"):
                if (tick // 4 + i) % 8 < 2:
                    p.fillRect(x, y, s, s, QColor(255, 255, 255, 18))

    def _cell_at(self, pos):
        main = self.main
        cx = int(pos.x() // main.cell)
        cy = int(pos.y() // main.cell)
        if 0 <= cx < main.gw and 0 <= cy < main.gh:
            return cy * main.gw + cx
        return -1

    def wheelEvent(self, e):
        main = self.main
        dy = e.angleDelta().y()
        if e.modifiers() & Qt.ControlModifier:
            main.set_zoom(main.cell + (2 if dy > 0 else -2))
            e.accept()
        elif e.modifiers() & Qt.ShiftModifier:
            bar = main.rscroll.horizontalScrollBar()
            bar.setValue(bar.value() - dy)
            e.accept()
        else:
            bar = main.rscroll.verticalScrollBar()
            bar.setValue(bar.value() - dy)
            e.accept()

    def mousePressEvent(self, e):
        main = self.main
        if main.model is None:
            return
        idx = self._cell_at(e.position())
        if idx < 0:
            return
        if e.button() == Qt.LeftButton:
            if main.zone_mode_btn.isChecked():
                cx, cy = idx % main.gw, idx // main.gw
                main.zone_drag = (cx, cy, cx, cy)
                self.update()
                return
            if main.pin_mode_btn.isChecked():
                main.push_undo()
                self._painting = True
                main.place_stroke(idx)
            else:
                main.on_board_click(idx)
        elif e.button() == Qt.RightButton:
            if main.zone_mode_btn.isChecked():
                main.remove_zone_at(idx)
                return
            main.on_board_click(idx, right=True)

    def mouseMoveEvent(self, e):
        main = self.main
        idx = self._cell_at(e.position())
        if idx != main.hover_idx:
            main.hover_idx = idx
            self.update()
        if main.zone_drag is not None and idx >= 0:
            x0, y0, _, _ = main.zone_drag
            main.zone_drag = (x0, y0, idx % main.gw, idx // main.gw)
            self.update()
            return
        if self._painting and main.pin_mode_btn.isChecked() and idx >= 0:
            main.place_stroke(idx, drag=True)
            return
        m = main.model
        if m and 0 <= idx < m.n and m.collapsed[idx]:
            t = main.tiles[m.tile_of[idx]]
            extra = ""
            if t.kind.startswith("fp_"):
                fcx, fcy = fp_cell(t.kind)
                extra = f" [cell {fcx},{fcy}"
                if t.kind in FP_ANCHOR_KINDS:
                    extra += f", R{t.rot * 90}°"
                extra += "]"
            nets = main.cell_nets.get(idx)
            ntxt = ""
            if nets:
                net = main.nets[nets[0]]
                ntxt = (f" — {net.name} ({len(net.cells)} cells, "
                        f"{'internal' if net.internal else main.sock_names.get(net.sock, '?')})")
            pin = " · pinned" if idx in main.pins else ""
            main.statusBar().showMessage(
                f"Probe ({idx % main.gw},{idx // main.gw}): {t.base}{extra}{pin}{ntxt}")
            return
        main.statusBar().clearMessage()

    def mouseReleaseEvent(self, e):
        main = self.main
        if e.button() == Qt.LeftButton and main.zone_drag is not None:
            main.commit_zone()
        self._painting = False

    def leaveEvent(self, e):
        main = self.main
        main.hover_idx = -1
        main.statusBar().clearMessage()
        self.update()


class PaletteRow(QWidget):
    def __init__(self, base, handler):
        super().__init__()
        self.base = base
        self._handler = handler
        self.setAttribute(Qt.WA_StyledBackground, True)

    def mouseReleaseEvent(self, e):
        self._handler(self.base)


# --------------------------------------------------------------------------- main window

QSS = """
* { font-size: 12px; }
QWidget { background-color: #14171c; color: #dfe5ec; }
QLabel { background: transparent; }
QGroupBox { border: 1px solid #2a313a; border-radius: 6px; margin-top: 10px; padding-top: 4px; }
QGroupBox::title { subcontrol-origin: margin; left: 8px; padding: 0 4px; color: #8fa3b8; }
QPushButton { background-color: #232a33; border: 1px solid #333c47; border-radius: 5px; padding: 5px 10px; }
QPushButton:hover { background-color: #2b343f; }
QPushButton:pressed { background-color: #1a2027; }
QPushButton:disabled { color: #5a6470; }
QSpinBox, QDoubleSpinBox, QComboBox { background-color: #1b2129; border: 1px solid #333c47; border-radius: 4px; padding: 3px 6px; }
QComboBox QAbstractItemView { background-color: #1b2129; selection-background-color: #2f5d3f; }
QSlider { background: transparent; }
QSlider::groove:horizontal { height: 4px; background: #2a313a; border-radius: 2px; }
QSlider::handle:horizontal { width: 12px; margin: -5px 0; background: #5aa2e8; border-radius: 6px; }
QScrollArea { border: none; background: transparent; }
QCheckBox { background: transparent; }
QTabWidget::pane { border: 1px solid #2a313a; }
QTabBar::tab { background: #1b2129; padding: 4px 12px; border: 1px solid #2a313a; }
QTabBar::tab:selected { background: #232a33; }
QListWidget, QTableWidget { background-color: #101419; border: 1px solid #2a313a; }
QHeaderView::section { background-color: #1b2129; border: none; padding: 3px; }
"""


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("WFC Circuit Studio — PCB & Logic + Analysis + MCTS + Footprints")
        self.resize(1320, 900)
        self.defn = BUILTIN["PCB board"]
        self.is_logic = False
        self.theme = PCB_THEME
        self.sock_names = self.defn.socket_names
        self.custom_defs = {}
        self.base_weights = dict(self.defn.weights)
        self.tiles = []
        self.prop = None
        self.model = None
        self.attempt = 0
        self.running = True
        self.note = None
        self.cell = 20
        self.speed = 8
        self.gw = self.gh = 32
        self.flashes = []
        self.nets = []
        self.node_net = {}
        self.cell_nets = {}
        self.ref_of = {}
        self.selected_net = None
        self.hover_idx = -1
        self.active_sockets = {1, 2, 3}
        self.was_done = False
        self.sim_vals = []
        self.sim_latch = []
        self.sim_ctr = []
        self.sim_clkp = []
        self.sim_sw = {}
        self.sim_tick = 0
        self.sim_dist = []
        self.solver_mcts = False
        self.mcts = None
        self.scratch = None
        self.pins = {}
        self.pin_base = None
        self.fp_rot = 0
        self.pin_rows = {}
        self.pin_conflicts = set()
        self.fp_placed = []
        self.fp_of_cell = {}
        self.fp_highlight = set()
        self.fp_var_cell = {}
        self.fp_anchor_variants = {}
        self.zones = []
        self._zone_mm = None
        self.zone_drag = None
        self.timeline = []
        self.tl_counts = []
        self.timeline_pos = -1
        self._undo = []
        self._redo = []
        self._build_ui()
        self.rebuild_weights_panel()
        self.rebuild_layer_checks()
        self.regen()
        self.run_btn.setText("Pause")
        self.timer = QTimer(self)
        self.timer.setInterval(16)
        self.timer.timeout.connect(self.tick)
        self.timer.start()
        for key, fn in ((Qt.Key_Space, self.toggle_run), (Qt.Key_S, self.on_step),
                        (Qt.Key_P, lambda: self.pin_mode_btn.toggle()),
                        (Qt.Key_Z, lambda: self.zone_mode_btn.toggle()),
                        (Qt.Key_G, lambda: self.show_grid.toggle()),
                        (Qt.Key_R, self.on_rotate_brush),
                        (QKeySequence("Ctrl+Z"), self.undo),
                        (QKeySequence("Ctrl+Y"), self.redo),
                        (QKeySequence("Ctrl+Shift+Z"), self.redo)):
            sc = QShortcut(QKeySequence(key), self)
            sc.activated.connect(fn)

    # ------------------------------------------------ UI

    def _build_ui(self):
        splitter = QSplitter(Qt.Horizontal)
        self.setCentralWidget(splitter)

        left_scroll = QScrollArea()
        left_scroll.setWidgetResizable(True)
        left_scroll.setFixedWidth(348)
        panel = QWidget()
        v = QVBoxLayout(panel)
        v.setContentsMargins(8, 8, 8, 8)
        v.setSpacing(8)

        box = QGroupBox("Setup")
        g = QGridLayout(box)
        g.addWidget(QLabel("Tileset"), 0, 0)
        self.set_combo = QComboBox()
        self.set_combo.addItems(["PCB board", "Logic circuit"])
        g.addWidget(self.set_combo, 0, 1)
        tsrow = QHBoxLayout()
        self.ts_load_btn = QPushButton("Load tileset…")
        self.ts_export_btn = QPushButton("Export JSON")
        self.ts_load_btn.setToolTip("Load a custom tileset from JSON "
                                    "(tiles, sockets, footprints, weights)")
        self.ts_export_btn.setToolTip("Dump the current tileset as a JSON template")
        for b in (self.ts_load_btn, self.ts_export_btn):
            b.setFocusPolicy(Qt.NoFocus)
            tsrow.addWidget(b)
        g.addLayout(tsrow, 1, 0, 1, 2)
        g.addWidget(QLabel("Solver"), 2, 0)
        self.solver_combo = QComboBox()
        self.solver_combo.addItems(["Classic (restart)", "MCTS (backtracking)"])
        g.addWidget(self.solver_combo, 2, 1)
        g.addWidget(QLabel("Explore C"), 3, 0)
        self.c_spin = QDoubleSpinBox()
        self.c_spin.setRange(0.1, 3.0)
        self.c_spin.setSingleStep(0.1)
        self.c_spin.setValue(1.4)
        g.addWidget(self.c_spin, 3, 1)
        self.outline_check = QCheckBox("Board outline (no edge bleed)")
        self.outline_check.setChecked(True)
        self.outline_check.setFocusPolicy(Qt.NoFocus)
        g.addWidget(self.outline_check, 4, 0, 1, 2)
        g.addWidget(QLabel("Width"), 5, 0)
        self.w_spin = QSpinBox(); self.w_spin.setRange(8, 64); self.w_spin.setValue(32)
        g.addWidget(self.w_spin, 5, 1)
        g.addWidget(QLabel("Height"), 6, 0)
        self.h_spin = QSpinBox(); self.h_spin.setRange(8, 64); self.h_spin.setValue(32)
        g.addWidget(self.h_spin, 6, 1)
        g.addWidget(QLabel("Seed"), 7, 0)
        self.seed_spin = QSpinBox(); self.seed_spin.setRange(0, 999999); self.seed_spin.setValue(1234)
        g.addWidget(self.seed_spin, 7, 1)
        dice = QPushButton("Random seed")
        dice.setFocusPolicy(Qt.NoFocus)
        g.addWidget(dice, 8, 0, 1, 2)
        g.addWidget(QLabel("Cell px"), 9, 0)
        self.cell_slider = QSlider(Qt.Horizontal)
        self.cell_slider.setRange(10, 36); self.cell_slider.setValue(20)
        self.cell_slider.setFocusPolicy(Qt.NoFocus)
        g.addWidget(self.cell_slider, 9, 1)
        g.addWidget(QLabel("Speed"), 10, 0)
        self.speed_slider = QSlider(Qt.Horizontal)
        self.speed_slider.setRange(1, 64); self.speed_slider.setValue(8)
        self.speed_slider.setFocusPolicy(Qt.NoFocus)
        g.addWidget(self.speed_slider, 10, 1)
        v.addWidget(box)

        tbox = QGroupBox("Generate")
        tg = QGridLayout(tbox)
        self.run_btn = QPushButton("Run"); self.run_btn.setFocusPolicy(Qt.NoFocus)
        self.step_btn = QPushButton("Step"); self.step_btn.setFocusPolicy(Qt.NoFocus)
        self.restart_btn = QPushButton("Restart"); self.restart_btn.setFocusPolicy(Qt.NoFocus)
        self.solve_btn = QPushButton("Solve now"); self.solve_btn.setFocusPolicy(Qt.NoFocus)
        self.save_btn = QPushButton("Save PNG"); self.save_btn.setFocusPolicy(Qt.NoFocus)
        self.svg_btn = QPushButton("Save SVG"); self.svg_btn.setFocusPolicy(Qt.NoFocus)
        self.svg_btn.setEnabled(HAS_SVG)
        self.best_btn = QPushButton("Best-of-N seeds"); self.best_btn.setFocusPolicy(Qt.NoFocus)
        self.n_spin = QSpinBox(); self.n_spin.setRange(2, 200); self.n_spin.setValue(12)
        self.route_btn = QPushButton("Autoroute stubs"); self.route_btn.setFocusPolicy(Qt.NoFocus)
        self.route_btn.setToolTip("A*-route open trace ends to each other through blank cells")
        self.autoroute_check = QCheckBox("Auto-repair after solve")
        self.autoroute_check.setChecked(True)
        self.autoroute_check.setFocusPolicy(Qt.NoFocus)
        self.proj_save_btn = QPushButton("Save project"); self.proj_save_btn.setFocusPolicy(Qt.NoFocus)
        self.proj_open_btn = QPushButton("Open project"); self.proj_open_btn.setFocusPolicy(Qt.NoFocus)
        tg.addWidget(self.run_btn, 0, 0)
        tg.addWidget(self.step_btn, 0, 1)
        tg.addWidget(self.restart_btn, 1, 0)
        tg.addWidget(self.solve_btn, 1, 1)
        tg.addWidget(self.save_btn, 2, 0)
        tg.addWidget(self.svg_btn, 2, 1)
        tg.addWidget(self.best_btn, 3, 0)
        tg.addWidget(self.n_spin, 3, 1)
        tg.addWidget(self.route_btn, 4, 0)
        tg.addWidget(self.autoroute_check, 4, 1)
        tg.addWidget(self.proj_save_btn, 5, 0)
        tg.addWidget(self.proj_open_btn, 5, 1)
        v.addWidget(tbox)

        zbox = QGroupBox("Zones")
        zv = QVBoxLayout(zbox)
        zrow = QHBoxLayout()
        self.zone_mode_btn = QCheckBox("Zone tool (Z)")
        self.zone_mode_btn.setToolTip("Drag a rectangle, the profile multiplies tile\n"
                                      "weights inside it during generation")
        self.zone_profile = QComboBox()
        self.zone_profile.addItems(list(ZONE_PROFILES.keys()))
        self.clear_zones_btn = QPushButton("Clear zones")
        for wdg in (self.zone_mode_btn, self.zone_profile, self.clear_zones_btn):
            wdg.setFocusPolicy(Qt.NoFocus)
        zrow.addWidget(self.zone_mode_btn); zrow.addWidget(self.zone_profile, 1)
        zrow.addWidget(self.clear_zones_btn)
        zv.addLayout(zrow)
        v.addWidget(zbox)

        tlbox = QGroupBox("Solve timeline")
        tv = QVBoxLayout(tlbox)
        trow = QHBoxLayout()
        self.tl_slider = QSlider(Qt.Horizontal)
        self.tl_slider.setRange(0, 0)
        self.tl_slider.setEnabled(False)
        self.tl_slider.setFocusPolicy(Qt.NoFocus)
        self.tl_label = QLabel("live")
        self.tl_export_btn = QPushButton("Export GIF")
        self.tl_export_btn.setFocusPolicy(Qt.NoFocus)
        trow.addWidget(self.tl_slider, 1); trow.addWidget(self.tl_label)
        trow.addWidget(self.tl_export_btn)
        tv.addLayout(trow)
        v.addWidget(tlbox)

        dbox = QGroupBox("Display")
        dv = QVBoxLayout(dbox)
        dg = QHBoxLayout()
        self.show_ghosts = QCheckBox("Ghosts"); self.show_ghosts.setChecked(True)
        self.show_grid = QCheckBox("Grid"); self.show_grid.setChecked(True)
        self.show_flash = QCheckBox("Flash"); self.show_flash.setChecked(True)
        for cb in (self.show_ghosts, self.show_grid, self.show_flash):
            cb.setFocusPolicy(Qt.NoFocus)
            dg.addWidget(cb)
        dv.addLayout(dg)
        prow = QHBoxLayout()
        self.pin_mode_btn = QCheckBox("Pin tool (P)")
        self.pin_size = QSpinBox()
        self.pin_size.setRange(1, 4); self.pin_size.setValue(1)
        self.pin_size.setToolTip("Pin brush size (square)")
        self.pin_size.setFocusPolicy(Qt.NoFocus)
        self.clear_pins_btn = QPushButton("Clear pins"); self.clear_pins_btn.setFocusPolicy(Qt.NoFocus)
        self.undo_btn = QPushButton("⟲"); self.undo_btn.setToolTip("Undo pin/zone edit (Ctrl+Z)")
        self.redo_btn = QPushButton("⟳"); self.redo_btn.setToolTip("Redo (Ctrl+Y)")
        for wdg in (self.clear_pins_btn, self.undo_btn, self.redo_btn):
            wdg.setFocusPolicy(Qt.NoFocus)
        prow.addWidget(self.pin_mode_btn); prow.addWidget(QLabel("Brush"))
        prow.addWidget(self.pin_size); prow.addWidget(self.clear_pins_btn)
        prow.addWidget(self.undo_btn); prow.addWidget(self.redo_btn)
        dv.addLayout(prow)
        self.sim_check = QCheckBox("Simulate (power/logic flow — click switches)")
        self.sim_check.setFocusPolicy(Qt.NoFocus)
        dv.addWidget(self.sim_check)
        v.addWidget(dbox)

        sbox = QGroupBox("Status")
        sg = QGridLayout(sbox)
        self.status_lbl = QLabel("Running")
        self.progress_lbl = QLabel("0%")
        self.restart_lbl = QLabel("0")
        self.mcts_lbl = QLabel("—")
        sg.addWidget(QLabel("State"), 0, 0); sg.addWidget(self.status_lbl, 0, 1)
        sg.addWidget(QLabel("Progress"), 1, 0); sg.addWidget(self.progress_lbl, 1, 1)
        sg.addWidget(QLabel("Restarts"), 2, 0); sg.addWidget(self.restart_lbl, 2, 1)
        sg.addWidget(QLabel("MCTS"), 3, 0); sg.addWidget(self.mcts_lbl, 3, 1)
        hint = QLabel("Pattern row = pin brush · ▣ chips stamp, R rotates · Z = zone drag\n"
                      "Ctrl+wheel zoom · wheel/Shift+wheel pan · minimap navigates\n"
                      "Space run · S step · P pins · Z zones · G grid · R rotate · Ctrl+Z/Y")
        hint.setWordWrap(True)
        sg.addWidget(hint, 4, 0, 1, 2)
        v.addWidget(sbox)

        wbox = QGroupBox("Tile weights (click a row to pick pin brush)")
        wv = QVBoxLayout(wbox)
        self.weights_scroll = QScrollArea()
        self.weights_scroll.setWidgetResizable(True)
        self.weights_scroll.setMinimumHeight(180)
        wv.addWidget(self.weights_scroll)
        v.addWidget(wbox, 1)

        left_scroll.setWidget(panel)
        splitter.addWidget(left_scroll)

        self.board = BoardWidget(self)
        rscroll = QScrollArea()
        rscroll.setWidgetResizable(False)
        rscroll.setAlignment(Qt.AlignCenter)
        rscroll.setWidget(self.board)
        self.rscroll = rscroll
        splitter.addWidget(rscroll)
        splitter.setStretchFactor(1, 1)

        self.minimap = Minimap(self, rscroll.viewport())
        self.minimap.raise_()
        rscroll.viewport().installEventFilter(self)
        self.reposition_minimap()

        self._build_dock()

        self.set_combo.currentTextChanged.connect(self.on_tileset)
        self.ts_load_btn.clicked.connect(self.load_tileset_file)
        self.ts_export_btn.clicked.connect(self.export_tileset_json)
        self.solver_combo.currentTextChanged.connect(lambda _: self.regen())
        self.outline_check.toggled.connect(lambda _: self.regen())
        self.w_spin.valueChanged.connect(lambda _: self.regen())
        self.h_spin.valueChanged.connect(lambda _: self.regen())
        self.seed_spin.editingFinished.connect(self.regen)
        dice.clicked.connect(self.on_random_seed)
        self.cell_slider.valueChanged.connect(self.set_zoom)
        self.speed_slider.valueChanged.connect(lambda val: setattr(self, "speed", val))
        self.run_btn.clicked.connect(self.toggle_run)
        self.step_btn.clicked.connect(self.on_step)
        self.restart_btn.clicked.connect(self.regen)
        self.solve_btn.clicked.connect(self.solve_now)
        self.best_btn.clicked.connect(self.best_of_n)
        self.route_btn.clicked.connect(lambda: (self.autoroute(), self.analyze()))
        self.save_btn.clicked.connect(self.save_png)
        self.svg_btn.clicked.connect(self.save_svg)
        self.tl_slider.valueChanged.connect(self.on_tl_slider)
        self.tl_export_btn.clicked.connect(self.export_timeline)
        self.zone_mode_btn.toggled.connect(self.on_zone_mode)
        self.clear_zones_btn.clicked.connect(self.clear_zones)
        self.proj_save_btn.clicked.connect(self.save_project)
        self.proj_open_btn.clicked.connect(self.open_project)
        self.clear_pins_btn.clicked.connect(self.clear_pins)
        self.undo_btn.clicked.connect(self.undo)
        self.redo_btn.clicked.connect(self.redo)
        self.pin_mode_btn.toggled.connect(self.on_pin_mode)
        for cb in (self.show_ghosts, self.show_grid, self.show_flash):
            cb.stateChanged.connect(self.board.update)

    def eventFilter(self, obj, ev):
        if obj is self.rscroll.viewport() and ev.type() == QEvent.Resize:
            self.reposition_minimap()
        return super().eventFilter(obj, ev)

    def reposition_minimap(self):
        vp = self.rscroll.viewport()
        m = self.minimap
        m.move(vp.width() - m.width() - 8, vp.height() - m.height() - 8)

    def _build_dock(self):
        dock = QDockWidget("Analysis", self)
        dock.setAllowedAreas(Qt.BottomDockWidgetArea | Qt.TopDockWidgetArea)
        dock.setFeatures(QDockWidget.DockWidgetFloatable | QDockWidget.DockWidgetMovable)
        tabs = QTabWidget()
        tabs.setDocumentMode(True)

        nets_w = QWidget()
        nv = QVBoxLayout(nets_w)
        nv.setContentsMargins(4, 4, 4, 4)
        self.net_info = QLabel("Solve a board to extract nets.")
        nv.addWidget(self.net_info)
        self.nets_list = QListWidget()
        self.nets_list.itemClicked.connect(self.on_net_clicked)
        nv.addWidget(self.nets_list, 1)
        nb = QHBoxLayout()
        self.analyze_btn = QPushButton("Analyze"); self.analyze_btn.setEnabled(False)
        self.clear_sel_btn = QPushButton("Clear selection")
        self.netlist_btn = QPushButton("Export netlist")
        self.vlog_btn = QPushButton("Export Verilog")
        for b in (self.clear_sel_btn, self.netlist_btn, self.vlog_btn):
            b.setFocusPolicy(Qt.NoFocus)
        nb.addWidget(self.analyze_btn); nb.addWidget(self.clear_sel_btn)
        nb.addWidget(self.netlist_btn); nb.addWidget(self.vlog_btn)
        nv.addLayout(nb)
        tabs.addTab(nets_w, "Nets")

        bom_w = QWidget()
        bv = QVBoxLayout(bom_w)
        bv.setContentsMargins(4, 4, 4, 4)
        self.bom_table = QTableWidget(0, 3)
        self.bom_table.setHorizontalHeaderLabels(["Refs", "Item", "Qty"])
        self.bom_table.horizontalHeader().setStretchLastSection(True)
        self.bom_table.setColumnWidth(0, 120)
        self.bom_table.setColumnWidth(1, 160)
        self.bom_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        bv.addWidget(self.bom_table, 1)
        bbtns = QHBoxLayout()
        self.csv_btn = QPushButton("Export CSV")
        bbtns.addStretch(1); bbtns.addWidget(self.csv_btn)
        bv.addLayout(bbtns)
        tabs.addTab(bom_w, "BOM")

        erc_w = QWidget()
        ev = QVBoxLayout(erc_w)
        ev.setContentsMargins(4, 4, 4, 4)
        self.erc_list = QListWidget()
        ev.addWidget(self.erc_list, 1)
        tabs.addTab(erc_w, "ERC")

        chips_w = QWidget()
        cv = QVBoxLayout(chips_w)
        cv.setContentsMargins(4, 4, 4, 4)
        cv.addWidget(QLabel("Placed multi-cell footprints — click to highlight:"))
        self.chips_list = QListWidget()
        self.chips_list.itemClicked.connect(self.on_chip_clicked)
        cv.addWidget(self.chips_list, 1)
        cb = QHBoxLayout()
        self.chip_remove_btn = QPushButton("Remove stamp")
        self.chip_remove_btn.setFocusPolicy(Qt.NoFocus)
        cb.addStretch(1); cb.addWidget(self.chip_remove_btn)
        cv.addLayout(cb)
        tabs.addTab(chips_w, "Chips")

        stats_w = QWidget()
        sh = QHBoxLayout(stats_w)
        sh.setContentsMargins(8, 8, 8, 8)
        stats_grid = QWidget()
        sg = QGridLayout(stats_grid)
        sg.setContentsMargins(0, 0, 0, 0)
        self.stat_lbls = {}
        for r, k in enumerate(["Nets", "Components", "Footprints", "Vias", "Trace cells",
                               "Stubs", "Gates", "Undriven nets", "Board fill"]):
            sg.addWidget(QLabel(k), r, 0)
            val = QLabel("—")
            self.stat_lbls[k] = val
            sg.addWidget(val, r, 1)
        sg.setColumnStretch(2, 1)
        sh.addWidget(stats_grid, 1)
        uv = QVBoxLayout()
        uv.addWidget(QLabel("Top patterns"))
        self.usage_list = QListWidget()
        uv.addWidget(self.usage_list, 1)
        uwrap = QWidget()
        uwrap.setLayout(uv)
        sh.addWidget(uwrap, 1)
        tabs.addTab(stats_w, "Stats")

        layers_w = QWidget()
        lv = QVBoxLayout(layers_w)
        lv.setContentsMargins(8, 8, 8, 8)
        self.layers_box = QVBoxLayout()
        lv.addLayout(self.layers_box)
        lab = QLabel("Untick a net class to fade it out of the view.")
        lab.setWordWrap(True)
        lv.addWidget(lab)
        lv.addStretch(1)
        tabs.addTab(layers_w, "Layers")

        dock.setWidget(tabs)
        dock.widget().setFixedHeight(200)
        self.addDockWidget(Qt.BottomDockWidgetArea, dock)

        self.analyze_btn.clicked.connect(self.analyze)
        self.clear_sel_btn.clicked.connect(self.clear_net_selection)
        self.netlist_btn.clicked.connect(self.export_netlist)
        self.vlog_btn.clicked.connect(self.export_verilog)
        self.csv_btn.clicked.connect(self.export_csv)
        self.chip_remove_btn.clicked.connect(self.remove_chip_stamp)

    # ------------------------------------------------ tilesets

    def switch_tileset(self, defn):
        self.defn = defn
        self.is_logic = defn.flavor == "logic"
        self.theme = defn.theme
        self.theme.bus_socket = defn.bus_socket
        self.sock_names = defn.socket_names
        self.base_weights = dict(defn.weights)
        self.pins.clear()
        self.pin_base = None
        self.board.pixcache.clear()
        self.rebuild_weights_panel()
        self.rebuild_layer_checks()

    def on_tileset(self, name):
        defn = self.custom_defs.get(name)
        if defn is None:
            defn = BUILTIN["Logic circuit"] if name.startswith("Logic") else BUILTIN["PCB board"]
        self.switch_tileset(defn)
        self.regen()

    def load_tileset_file(self):
        path, _ = QFileDialog.getOpenFileName(self, "Load tileset JSON", "",
                                              "Tileset JSON (*.json)")
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                d = json.load(f)
            defn = tileset_from_dict(d)
        except Exception as ex:
            self.statusBar().showMessage(f"Tileset load failed: {ex}", 6000)
            return
        name = defn.name
        k = 2
        while name in self.custom_defs or name in BUILTIN:
            name = f"{defn.name} ({k})"
            k += 1
        defn.name = name
        self.custom_defs[name] = defn
        self.set_combo.addItem(name)
        self.set_combo.setCurrentText(name)
        self.statusBar().showMessage(
            f"Tileset loaded: {name} ({len(defn.singles)} tiles, {len(defn.fps)} footprints)", 6000)

    def export_tileset_json(self):
        d = tileset_to_dict(self.defn, self.base_weights)
        path, _ = QFileDialog.getSaveFileName(self, "Export tileset JSON",
                                              "tileset.json", "Tileset JSON (*.json)")
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(d, f, indent=1)
            self.statusBar().showMessage(f"Tileset exported: {path}", 5000)
        except OSError as ex:
            self.statusBar().showMessage(f"Export failed: {ex}", 5000)

    # ------------------------------------------------ model / solver management

    def compute_zone_mults(self):
        if not self.zones:
            return None
        T = len(self.tiles)
        multmap = {}
        for (x0, y0, x1, y1, pname) in self.zones:
            prof = ZONE_PROFILES.get(pname, {})
            for y in range(min(y0, y1), max(y0, y1) + 1):
                for x in range(min(x0, x1), max(x0, x1) + 1):
                    ml = multmap.setdefault(y * self.gw + x, [1.0] * T)
                    for ti, t in enumerate(self.tiles):
                        ml[ti] *= prof.get(kind_class(t.kind), 1.0)
        return multmap or None

    def apply_zones(self):
        self._zone_mm = self.compute_zone_mults()
        for mdl in (self.model, self.scratch):
            if mdl is not None:
                mdl.set_zone_weights(self._zone_mm)
        if self.solver_mcts and self.model is not None:
            self.reset_solver()
        self.board.update()

    def make_seed_model(self, seed_key):
        m = WFCModel(self.gw, self.gh, self.tiles,
                     [t.weight for t in self.tiles],
                     random.Random(seed_key), self.prop)
        if self.outline_check.isChecked():
            m.apply_border()
        if self._zone_mm:
            m.set_zone_weights(self._zone_mm)
        if self.pins:
            try:
                self._apply_pins(m)
            except Contradiction:
                self.pin_conflicts = set(self.pins)
                m = WFCModel(self.gw, self.gh, self.tiles,
                             [t.weight for t in self.tiles],
                             random.Random(seed_key), self.prop)
                if self.outline_check.isChecked():
                    m.apply_border()
                if self._zone_mm:
                    m.set_zone_weights(self._zone_mm)
        return m

    def _apply_pins(self, m):
        if not self.pins:
            return
        self.pin_conflicts = set()
        for idx in sorted(self.pins):
            base, rot = self.pins[idx]
            if base in FP_INFO:
                variants = [ti for ti, t in enumerate(self.tiles)
                            if t.base == base and t.kind in FP_ANCHOR_KINDS
                            and t.rot == rot and (m.mask[idx] >> ti) & 1]
            else:
                variants = [ti for ti, t in enumerate(self.tiles)
                            if t.base == base and (m.mask[idx] >> ti) & 1]
            if not variants:
                self.pin_conflicts.add(idx)
                continue
            m.collapse(idx, self._weighted_variant(m, variants))
            m.propagate((idx,))

    def make_model(self):
        return self.make_seed_model(f"{self.seed}:{self.attempt}")

    @staticmethod
    def _weighted_variant(m, variants):
        tot = sum(m.weights[v] for v in variants)
        x = m.rng.random() * tot
        acc = 0.0
        for v in variants:
            acc += m.weights[v]
            if x < acc:
                return v
        return variants[-1]

    def reset_solver(self):
        if self.model is None or not self.solver_mcts:
            self.mcts = None
            self.scratch = None
            return
        self.scratch = self.make_seed_model(f"{self.seed}:{self.attempt}")
        self.mcts = MCTSSolver(self.model.snapshot(), c=self.c_spin.value())
        self.mcts_lbl.setText("it=0 · nodes=1 · best=—")

    def regen(self):
        self.gw, self.gh = self.w_spin.value(), self.h_spin.value()
        self.seed = self.seed_spin.value()
        self.solver_mcts = self.solver_combo.currentText().startswith("MCTS")
        self.tiles = build_tiles(self.defn, self.base_weights)
        self.prop = build_prop_tables(self.tiles)
        self._zone_mm = self.compute_zone_mults()
        self.fp_var_cell = {}
        self.fp_anchor_variants = {}
        for ti, t in enumerate(self.tiles):
            if t.kind.startswith("fp_"):
                if t.kind in FP_ANCHOR_KINDS:
                    self.fp_anchor_variants.setdefault((t.base, t.rot), []).append(ti)
                else:
                    cx, cy = fp_cell(t.kind)
                    self.fp_var_cell[(t.base, t.rot, cx, cy)] = ti
        self.attempt = 0
        self.note = None
        self.flashes.clear()
        self.pin_conflicts = set()
        self.fp_highlight = set()
        self.fp_placed = []
        self.fp_of_cell = {}
        self.model = self.make_model()
        self.was_done = False
        self.nets = []
        self.node_net = {}
        self.cell_nets = {}
        self.ref_of = {}
        self.selected_net = None
        self.hover_idx = -1
        self.sim_vals = [0] * self.model.n
        self.sim_latch = [False] * self.model.n
        self.sim_ctr = [i % 16 for i in range(self.model.n)]
        self.sim_clkp = [False] * self.model.n
        self.sim_sw = {}
        self.sim_dist = []
        self.timeline = []
        self.tl_counts = []
        self.timeline_pos = -1
        self.tl_slider.blockSignals(True)
        self.tl_slider.setRange(0, 0)
        self.tl_slider.setValue(0)
        self.tl_slider.setEnabled(False)
        self.tl_slider.blockSignals(False)
        self.tl_label.setText("live")
        self.tl_export_btn.setEnabled(False)
        self.analyze_btn.setEnabled(False)
        self.net_info.setText("Solve a board to extract nets.")
        self.reset_solver()
        if not self.solver_mcts:
            self.mcts_lbl.setText("— (classic mode)")
        self.board.invalidate_layer()
        self.board.setFixedSize(self.gw * self.cell, self.gh * self.cell)
        self.reposition_minimap()
        self.update_stats()
        self.board.update()

    # ------------------------------------------------ main loop

    def paint_view(self):
        if 0 <= self.timeline_pos < len(self.timeline):
            return TLView(self.timeline[self.timeline_pos], self.model.n)
        return self.model

    def timeline_active(self):
        return 0 <= self.timeline_pos < len(self.timeline)

    def _record_timeline(self, force=False):
        m = self.model
        if m is None:
            return
        c = sum(m.collapsed)
        if not force and self.timeline and c == self.tl_counts[-1]:
            return
        step = max(1, m.n // 48)
        if force or not self.timeline or c - self.tl_counts[-1] >= step or c == m.n:
            self.timeline.append(m.tile_of[:])
            self.tl_counts.append(c)
            was_live = self.tl_slider.value() >= self.tl_slider.maximum()
            self.tl_slider.blockSignals(True)
            self.tl_slider.setRange(0, len(self.timeline))
            if was_live:
                self.tl_slider.setValue(len(self.timeline))
            self.tl_slider.blockSignals(False)
            self.tl_slider.setEnabled(True)
            self.tl_export_btn.setEnabled(len(self.timeline) >= 2)
            self.update_tl_label()

    def on_tl_slider(self, val):
        if val >= len(self.timeline):
            self.timeline_pos = -1
        else:
            self.timeline_pos = val
            if self.running:
                self.toggle_run()
        self.update_tl_label()
        self.board.update()

    def update_tl_label(self):
        v = self.tl_slider.value()
        if v >= len(self.timeline) or not self.tl_counts:
            self.tl_label.setText("live")
        else:
            self.tl_label.setText(f"f{v}/{len(self.timeline)} · {self.tl_counts[v]}")

    def tick(self):
        if self.running and self.model is not None and not self.model.is_done():
            if self.solver_mcts:
                self.mcts_step_batch(max(1, self.speed))
            else:
                for _ in range(self.speed):
                    if not self.do_step():
                        break
        m = self.model
        if m is not None:
            done = m.is_done()
            if done and not self.was_done:
                self.was_done = True
                if self.autoroute_check.isChecked():
                    self.autoroute(quiet=True)
                self._record_timeline(force=True)
                self.analyze()
                self.analyze_btn.setEnabled(True)
            elif not done and self.was_done:
                self.was_done = False
                self.analyze_btn.setEnabled(False)
                self.nets = []
                self.node_net = {}
                self.cell_nets = {}
                self.ref_of = {}
                self.selected_net = None
            if done and self.sim_check.isChecked() and not self.timeline_active():
                for _ in range(2):
                    self.sim_iter()
                self.sim_tick += 1
        if self.flashes:
            now = time.monotonic()
            self.flashes = [(i, t) for (i, t) in self.flashes if now - t < 0.4]
        self.update_stats()
        self.board.update()
        self.minimap.update()

    def mcts_step_batch(self, k):
        t0 = time.monotonic()
        solved = False
        for _ in range(k):
            self.mcts.iterate(self.scratch)
            if self.mcts.solved_snap is not None:
                solved = True
                break
            if time.monotonic() - t0 > 0.025:
                break
        snap = self.mcts.solved_snap if solved else self.mcts.best_snap
        if snap is not None:
            old = {i for i in range(self.model.n) if self.model.collapsed[i]}
            self.model.restore(snap)
            self._record_timeline()
            if self.show_flash.isChecked():
                now = time.monotonic()
                added = 0
                for i in range(self.model.n):
                    if self.model.collapsed[i] and i not in old:
                        self.flashes.append((i, now))
                        added += 1
                        if added >= 120:
                            break
        pc = 100.0 * self.mcts.best_done / max(self.model.n, 1)
        lbl = f"it={self.mcts.iters} · nodes={self.mcts.nodes} · best={pc:.0f}%"
        if solved:
            lbl += " · SOLVED"
            self.running = False
            self.run_btn.setText("Run")
        self.mcts_lbl.setText(lbl)

    def do_step(self):
        m = self.model
        if m is None or m.is_done():
            return False
        if self.solver_mcts:
            self.mcts_step_batch(1)
            return not m.is_done()
        try:
            i = m.step()
            if i is None:
                return False
            self._record_timeline()
            if self.show_flash.isChecked():
                self.flashes.append((i, time.monotonic()))
        except Contradiction:
            self._on_contradiction()
        return not m.is_done()

    def _on_contradiction(self):
        self.attempt += 1
        if self.attempt > MAX_ATTEMPTS:
            self.model.fill_remaining()
            self.running = False
            self.run_btn.setText("Run")
            self.note = "Stopped (filled leftovers)"
        else:
            self.model = self.make_model()
            if self.solver_mcts:
                self.reset_solver()

    # ------------------------------------------------ autorouter

    def autoroute(self, quiet=False):
        m = self.model
        if m is None or not m.is_done():
            if not quiet:
                self.statusBar().showMessage("Finish solving first", 3000)
            return 0
        n = autoroute_stubs(m, self.tiles, self.gw, self.gh)
        if n:
            self.board.invalidate_layer()
            self._record_timeline(force=True)
            if not quiet:
                self.statusBar().showMessage(f"Autorouter: repaired {n} open end(s)", 5000)
        elif not quiet:
            self.statusBar().showMessage("Autorouter: no open ends found", 4000)
        return n

    # ------------------------------------------------ pins + zones + undo

    def push_undo(self):
        self._undo.append((dict(self.pins), list(self.zones)))
        if len(self._undo) > 60:
            self._undo.pop(0)
        self._redo.clear()

    def undo(self):
        if not self._undo:
            return
        self._redo.append((dict(self.pins), list(self.zones)))
        self.pins, self.zones = self._undo.pop()
        self.apply_zones()
        self.regen()

    def redo(self):
        if not self._redo:
            return
        self._undo.append((dict(self.pins), list(self.zones)))
        self.pins, self.zones = self._redo.pop()
        self.apply_zones()
        self.regen()

    def on_pin_mode(self, on):
        if on:
            self.zone_mode_btn.setChecked(False)
        self.board.setCursor(Qt.CrossCursor if (on or self.zone_mode_btn.isChecked())
                             else Qt.ArrowCursor)
        self.board.update()

    def on_zone_mode(self, on):
        if on:
            self.pin_mode_btn.setChecked(False)
        self.board.setCursor(Qt.CrossCursor if (on or self.pin_mode_btn.isChecked())
                             else Qt.ArrowCursor)
        self.board.update()

    def on_rotate_brush(self):
        if self.pin_base in FP_INFO:
            self.fp_rot = (self.fp_rot + 1) % 4
            self.statusBar().showMessage(
                f"Footprint brush rotation: {self.fp_rot * 90}° (R to cycle)", 3000)
            self.board.update()

    def on_pick_brush(self, base):
        self.pin_base = base
        for b, row in self.pin_rows.items():
            row.setStyleSheet("border:1px solid #5aa2e8; border-radius:4px;"
                              if b == base else "")
        self.pin_mode_btn.setChecked(True)
        if base in FP_INFO:
            kind = f"stamps the whole footprint ({self.fp_rot * 90}° — R rotates)"
        else:
            kind = "click/drag cells to pin"
        self.statusBar().showMessage(
            f"Pin brush: {base} — {kind}, right-click removes (P toggles)", 5000)

    def brush_cells(self, idx):
        b = self.pin_size.value()
        if b <= 1:
            return [idx]
        r = b // 2
        x0, y0 = idx % self.gw, idx // self.gw
        out = []
        for dy in range(-(b - 1 - r), r + 1):
            for dx in range(-(b - 1 - r), r + 1):
                x, y = x0 + dx, y0 + dy
                if 0 <= x < self.gw and 0 <= y < self.gh:
                    out.append(y * self.gw + x)
        return out

    def place_stroke(self, idx, drag=False):
        base = self.pin_base
        if base is None:
            self.statusBar().showMessage(
                "Pick a pin brush: click a pattern in the weights panel", 4000)
            return
        if base in FP_INFO:
            if drag:
                return
            if self.pins.get(idx, (None, 0))[0] == base:
                return
            self.pins[idx] = (base, self.fp_rot)
            self._apply_single_pin(idx, quiet=False)
            self.statusBar().showMessage(
                f"Stamped {base} @ {self.fp_rot * 90}° at ({idx % self.gw},{idx // self.gw})", 3000)
            self.update_stats()
            self.board.update()
            return
        for cell in self.brush_cells(idx):
            if cell in self.pins and self.pins[cell][0] == base:
                continue
            self.pins[cell] = (base, 0)
            self._apply_single_pin(cell, quiet=True)
        self.update_stats()
        self.board.update()

    def _apply_single_pin(self, idx, quiet=True):
        m = self.model
        base, rot = self.pins[idx]
        if base in FP_INFO:
            variants = [ti for ti, t in enumerate(self.tiles)
                        if t.base == base and t.kind in FP_ANCHOR_KINDS
                        and t.rot == rot and (m.mask[idx] >> ti) & 1]
        else:
            variants = [ti for ti, t in enumerate(self.tiles)
                        if t.base == base and (m.mask[idx] >> ti) & 1]
        if not variants:
            if not quiet:
                self.statusBar().showMessage(
                    "Pin conflicts here — it will apply on the next restart", 3000)
            return
        try:
            m.collapse_to(idx, self._weighted_variant(m, variants))
            m.close_forced()
            if self.show_flash.isChecked():
                self.flashes.append((idx, time.monotonic()))
        except Contradiction:
            if not quiet:
                self.statusBar().showMessage("Pin caused a contradiction — new attempt", 3000)
            self._on_contradiction()
        if self.solver_mcts:
            self.reset_solver()
        if m.is_done() and not self.was_done:
            self.was_done = True
            self.analyze()
            self.analyze_btn.setEnabled(True)

    def clear_pins(self):
        if self.pins:
            self.push_undo()
            self.pins.clear()
            self.regen()

    def commit_zone(self):
        if self.zone_drag is None:
            return
        x0, y0, x1, y1 = self.zone_drag
        self.zone_drag = None
        x0, x1 = min(x0, x1), max(x0, x1)
        y0, y1 = min(y0, y1), max(y0, y1)
        pname = self.zone_profile.currentText()
        self.push_undo()
        self.zones.append((x0, y0, x1, y1, pname))
        self.apply_zones()
        self.statusBar().showMessage(
            f"Zone added: {pname} ({x1 - x0 + 1}×{y1 - y0 + 1} at {x0},{y0})", 4000)

    def remove_zone_at(self, idx):
        x, y = idx % self.gw, idx // self.gw
        for k in range(len(self.zones) - 1, -1, -1):
            zx0, zy0, zx1, zy1, _p = self.zones[k]
            if zx0 <= x <= zx1 and zy0 <= y <= zy1:
                self.push_undo()
                removed = self.zones.pop(k)
                self.apply_zones()
                self.statusBar().showMessage(f"Removed zone: {removed[4]}", 3000)
                return

    def clear_zones(self):
        if self.zones:
            self.push_undo()
            self.zones.clear()
            self.apply_zones()

    # ------------------------------------------------ board interaction

    def on_board_click(self, idx, right=False):
        m = self.model
        if m is None:
            return
        if right and self.pin_mode_btn.isChecked():
            if idx in self.pins:
                self.push_undo()
                if self.pins[idx][0] in FP_INFO:
                    del self.pins[idx]
                else:
                    for cell in self.brush_cells(idx):
                        self.pins.pop(cell, None)
                self.regen()
            return
        if not m.collapsed[idx]:
            if right:
                return
            try:
                seeds = m.collapse(idx)
                m.propagate(seeds)
                if self.show_flash.isChecked():
                    self.flashes.append((idx, time.monotonic()))
            except Contradiction:
                self._on_contradiction()
            self.update_stats()
            self.board.update()
            return
        t = self.tiles[m.tile_of[idx]]
        if t.kind == "switch":
            self.sim_sw[idx] = not self._sw(idx)
            self.compute_sim_dist()
            self.board.update()
            return
        if right:
            return
        if m.is_done():
            nets = self.cell_nets.get(idx)
            if nets:
                nid = nets[0]
                self.selected_net = None if self.selected_net == nid else nid
                self.show_net_info()
                self.board.update()

    def clear_net_selection(self):
        self.selected_net = None
        self.show_net_info()
        self.board.update()

    def show_net_info(self):
        if self.selected_net is None:
            self.net_info.setText("Click a trace to highlight its net.")
        else:
            net = self.nets[self.selected_net]
            kn = "internal" if net.internal else self.sock_names.get(net.sock, "?")
            self.net_info.setText(f"Selected: {net.name} — {len(net.cells)} cells ({kn})")

    def toggle_run(self):
        if self.model is None:
            return
        if self.timeline_pos >= 0:
            self.tl_slider.setValue(len(self.timeline))
        if self.model.is_done():
            self.regen()
            self.running = True
        else:
            self.running = not self.running
        self.run_btn.setText("Pause" if self.running else "Run")
        self.update_stats()
        self.board.update()

    def on_step(self):
        self.running = False
        self.run_btn.setText("Run")
        self.do_step()
        self.update_stats()
        self.board.update()

    def solve_now(self):
        if self.model is None:
            return
        QApplication.setOverrideCursor(Qt.WaitCursor)
        try:
            if self.solver_mcts:
                guard = 0
                while not self.model.is_done() and guard < 120000:
                    self.mcts.iterate(self.scratch)
                    guard += 1
                    if self.mcts.solved_snap is not None:
                        break
                    if guard % 600 == 0:
                        if self.mcts.best_snap is not None:
                            self.model.restore(self.mcts.best_snap)
                        self.update_stats()
                        self.board.update()
                        QApplication.processEvents()
                if self.mcts.solved_snap is not None:
                    self.model.restore(self.mcts.solved_snap)
                elif self.mcts.best_snap is not None:
                    self.model.restore(self.mcts.best_snap)
                if not self.model.is_done():
                    self.note = "Search budget exhausted"
                pc = 100.0 * self.mcts.best_done / max(self.model.n, 1)
                self.mcts_lbl.setText(f"it={self.mcts.iters} · nodes={self.mcts.nodes} · best={pc:.0f}%")
            else:
                guard = 0
                while not self.model.is_done() and guard < 400000:
                    guard += 1
                    try:
                        if self.model.step() is None:
                            break
                        self._record_timeline()
                    except Contradiction:
                        self.attempt += 1
                        if self.attempt > MAX_ATTEMPTS:
                            self.model.fill_remaining()
                            self.note = "Stopped (filled leftovers)"
                            break
                        self.model = self.make_model()
            self.running = False
            self.run_btn.setText("Run")
        finally:
            QApplication.restoreOverrideCursor()
        self.update_stats()
        self.board.update()

    # ------------------------------------------------ design explorer (best-of-N)

    def net_driven(self, sock, kinds):
        if sock >= INNER_BASE:
            return True
        if not self.is_logic:
            if sock == 2:
                return any(k in ("source", "battery") for k in kinds)
            if sock == 3:
                return "gndsym" in kinds
            return False
        bus = self.theme.bus_socket
        if bus and bus in kinds:
            return True
        if sock == 2:
            return bool(kinds & {"clocksrc", "xtal", "gate_pll"})
        return bool(kinds & {"source", "gndsym", "switch"})

    def score_board(self, model):
        groups, _ = extract_net_groups(model, self.tiles, self.gw, self.gh)
        undriven = stubs = comps = 0
        for cells, sock, kinds in groups:
            if sock >= INNER_BASE:
                continue
            if not self.net_driven(sock, kinds):
                undriven += 1
            if len(cells) == 1:
                stubs += 1
            comps += sum(1 for i in cells
                         if self.tiles[model.tile_of[i]].kind in COMP_KINDS)
        filled = sum(model.collapsed) / max(model.n, 1)
        return (comps * 1.0 + len(groups) * 0.1 + filled * 2.0
                - undriven * 3.0 - stubs * 0.5)

    def best_of_n(self):
        QApplication.setOverrideCursor(Qt.WaitCursor)
        self.running = False
        self.run_btn.setText("Run")
        best_seed, best_score, best_model = self.seed_spin.value(), -1e18, None
        try:
            n = self.n_spin.value()
            base_seed = self.seed_spin.value()
            for k in range(n):
                seed = (base_seed + k * 7919) % 1000000
                model = self.make_seed_model(f"{seed}:0")
                guard = 0
                try:
                    while not model.is_done() and guard < 200000:
                        guard += 1
                        if model.step() is None:
                            break
                except Contradiction:
                    pass
                if not model.is_done():
                    model.fill_remaining()
                score = self.score_board(model)
                if score > best_score:
                    best_score, best_seed, best_model = score, seed, model
                if k % 2 == 1:
                    self.statusBar().showMessage(
                        f"Best-of-N: {k + 1}/{n} candidates…  best score {best_score:.1f}")
                    QApplication.processEvents()
            self.seed_spin.setValue(best_seed)
            self.regen()
            if best_model is not None:
                m = self.model
                for i in range(m.n):
                    tv = best_model.tile_of[i]
                    w = m.weights[tv]
                    m.mask[i] = 1 << tv
                    m.count[i] = 1
                    m.sumw[i] = w
                    m.sumwlog[i] = m.logw[tv] * w
                    m.collapsed[i] = True
                    m.tile_of[i] = tv
                m.rebuild_heap()
                self.autoroute(quiet=True)
                self._record_timeline(force=True)
                self.was_done = True
                self.analyze()
                self.analyze_btn.setEnabled(True)
                self.reset_solver()
            self.statusBar().showMessage(
                f"Best-of-N: picked seed {best_seed} (score {best_score:.1f})", 6000)
        finally:
            QApplication.restoreOverrideCursor()
        self.update_stats()
        self.board.update()

    # ------------------------------------------------ simulator

    def sim_active(self):
        return (self.model is not None and self.model.is_done()
                and self.sim_check.isChecked() and bool(self.sim_vals))

    def _sw(self, i):
        return self.sim_sw.get(i, i % 3 == 0)

    def _conn(self, i, d):
        m = self.model
        t = self.tiles[m.tile_of[i]]
        s = t.edges[d]
        if not s:
            return None
        x, y = i % self.gw, i // self.gw
        nx, ny = x + DIRS[d][0], y + DIRS[d][1]
        if not (0 <= nx < self.gw and 0 <= ny < self.gh):
            return None
        j = ny * self.gw + nx
        if self.tiles[m.tile_of[j]].edges[(d + 2) % 4] != s:
            return None
        return j

    def compute_sim_dist(self):
        m = self.model
        if m is None:
            return
        dist = [10 ** 6] * m.n
        dq = deque()
        for i in range(m.n):
            if not m.collapsed[i]:
                continue
            k = self.tiles[m.tile_of[i]].kind
            if k in ("source", "battery", "clocksrc", "xtal") or (
                    k.startswith("fp_") and k[3:].split("_")[0] in FP_ACTIVE):
                dist[i] = 0
                dq.append(i)
        while dq:
            i = dq.popleft()
            for d in range(4):
                j = self._conn(i, d)
                if j is not None and dist[j] > dist[i] + 1:
                    dist[j] = dist[i] + 1
                    dq.append(j)
        self.sim_dist = dist

    def sim_iter(self):
        m = self.model
        prev = self.sim_vals
        new = prev[:]
        for i in range(m.n):
            if not m.collapsed[i]:
                new[i] = 0
                continue
            t = self.tiles[m.tile_of[i]]
            k = t.kind
            if k in ("source", "battery"):
                new[i] = 1
            elif k == "gndsym":
                new[i] = 0
            elif k == "clocksrc":
                new[i] = (self.sim_tick // 3) % 2
            elif k == "xtal":
                new[i] = ((self.sim_tick + i) // 3) % 2
            elif k == "switch":
                new[i] = 1 if self._sw(i) else 0
            elif k.startswith("gate_"):
                new[i] = self._gate_eval(i, t, k, prev)
            elif k.startswith("fp_"):
                slug = k[3:].split("_")[0]
                if slug in ("cpu", "gpu"):
                    new[i] = (self.sim_tick // 4) % 2
                elif slug in ("uart", "timer", "osc"):
                    new[i] = ((self.sim_tick + i) // 3) % 2
                else:
                    v = 0
                    for d in range(4):
                        if t.edges[d] in (1, 2, 3):
                            j = self._conn(i, d)
                            if j is not None and prev[j]:
                                v = 1
                                break
                    new[i] = v
            else:
                v = 0
                for d in range(4):
                    if t.edges[d] in (1, 2, 3):
                        j = self._conn(i, d)
                        if j is not None and prev[j]:
                            v = 1
                            break
                new[i] = v
        self.sim_vals = new

    def _gate_eval(self, i, t, kind, prev):
        out = (GATE_STYLE[kind][2] + t.rot) % 4
        sig, clk = [], []
        for d in range(4):
            if not t.edges[d] or d == out:
                continue
            j = self._conn(i, d)
            v = bool(prev[j]) if j is not None else False
            (clk if t.edges[d] == 2 else sig).append(v)
        if kind in ("gate_reg", "gate_ctr"):
            c = bool(clk and clk[0])
            rising = c and not self.sim_clkp[i]
            self.sim_clkp[i] = c
            if rising:
                if kind == "gate_reg":
                    self.sim_latch[i] = any(sig)
                else:
                    self.sim_ctr[i] = (self.sim_ctr[i] + 1) & 0xF
            return self.sim_latch[i] if kind == "gate_reg" else bool(self.sim_ctr[i] & 1)
        if kind == "gate_pll":
            return any(clk)
        if kind in ("gate_and", "gate_nand"):
            v = bool(sig) and all(sig)
            return (not v) if kind == "gate_nand" else v
        if kind in ("gate_or", "gate_nor"):
            v = any(sig)
            return (not v) if kind == "gate_nor" else v
        if kind == "gate_xor":
            return sum(sig) % 2 == 1
        if kind == "gate_xnor":
            return sum(sig) % 2 == 0
        if kind == "gate_not":
            return not (sig[0] if sig else 0)
        if kind in ("gate_buf", "gate_tri"):
            return bool(sig and sig[0])
        if kind == "gate_cmp":
            return len(sig) >= 2 and sig[0] == sig[1]
        if kind == "gate_add":
            return len(sig) >= 2 and (sig[0] ^ sig[1])
        return any(sig)

    # ------------------------------------------------ analysis

    def fp_group_cells(self, anchor_idx):
        m = self.model
        base = self.tiles[m.tile_of[anchor_idx]].base
        seen = {anchor_idx}
        dq = deque([anchor_idx])
        while dq:
            i = dq.popleft()
            for d in range(4):
                s = self.tiles[m.tile_of[i]].edges[d]
                if s < INNER_BASE:
                    continue
                j = self._conn(i, d)
                if j is not None and j not in seen \
                        and self.tiles[m.tile_of[j]].base == base:
                    seen.add(j)
                    dq.append(j)
        return seen

    def analyze(self):
        m = self.model
        if m is None or not m.is_done():
            return
        groups, node_net = extract_net_groups(m, self.tiles, self.gw, self.gh)
        self.node_net = node_net
        counters = defaultdict(int)
        nets = []
        for cells, sock, kinds in sorted(groups, key=lambda g: -len(g[0])):
            internal = sock >= INNER_BASE
            if not self.is_logic:
                pre = "PWR" if sock == 2 else ("GND" if sock == 3 else "NET")
            else:
                bus = self.theme.bus_socket
                if internal:
                    pre = "INT"
                elif bus and bus in kinds:
                    pre = "BUS"
                elif sock == 2:
                    pre = "CLK"
                elif "source" in kinds:
                    pre = "VCC"
                elif "gndsym" in kinds:
                    pre = "GND"
                elif "switch" in kinds:
                    pre = "SW"
                else:
                    pre = "NET"
            driven = self.net_driven(sock, kinds)
            counters[pre] += 1
            comps = sum(1 for i in cells if self.tiles[m.tile_of[i]].kind in COMP_KINDS)
            nets.append(Net(f"{pre}{counters[pre]}", sock, cells, kinds, driven,
                            comps, internal))
        self.nets = nets
        self.cell_nets = defaultdict(list)
        for nid, net in enumerate(nets):
            for i in net.cells:
                self.cell_nets[i].append(nid)
        self.cell_nets = dict(self.cell_nets)
        self.ref_of = {}
        refctr = defaultdict(int)
        for i in range(m.n):
            k = self.tiles[m.tile_of[i]].kind
            if k in COMP_KINDS:
                pfx = KIND_PREFIX.get(k, "U")
                refctr[pfx] += 1
                self.ref_of[i] = f"{pfx}{refctr[pfx]}"
        self.fp_placed = []
        self.fp_of_cell = {}
        seen_anchors = set()
        for i in range(m.n):
            if not m.collapsed[i]:
                continue
            t = self.tiles[m.tile_of[i]]
            if t.kind not in FP_ANCHOR_KINDS or i in seen_anchors:
                continue
            cells = self.fp_group_cells(i)
            for c in cells:
                if self.tiles[m.tile_of[c]].kind in FP_ANCHOR_KINDS:
                    seen_anchors.add(c)
            pin_count = sum(1 for c in cells
                            for e in self.tiles[m.tile_of[c]].edges if e in (1, 2, 3))
            entry = dict(anchor=i, base=t.base, rot=t.rot, cells=cells,
                         ref=self.ref_of.get(i, "?"), pins=pin_count)
            self.fp_placed.append(entry)
            for c in cells:
                self.fp_of_cell[c] = entry
        self.selected_net = None
        self.populate_nets()
        self.populate_erc()
        self.populate_bom()
        self.populate_stats()
        self.populate_chips()
        self.show_net_info()
        self.compute_sim_dist()

    def populate_nets(self):
        self.nets_list.clear()
        rows = sorted(range(len(self.nets)), key=lambda n: -len(self.nets[n].cells))
        for nid in rows[:400]:
            net = self.nets[nid]
            if net.internal:
                continue
            warn = (self.is_logic and net.sock in (1, 2)
                    and not net.driven and len(net.cells) >= 2)
            txt = (f"{net.name}  ·  {len(net.cells)} cells  ·  "
                   f"{self.sock_names.get(net.sock, '?')}  ·  {net.comps} parts")
            if warn:
                txt += "   ⚠ undriven"
            it = QListWidgetItem(txt)
            it.setData(Qt.UserRole, nid)
            self.nets_list.addItem(it)

    def on_net_clicked(self, item):
        nid = item.data(Qt.UserRole)
        self.selected_net = nid
        self.show_net_info()
        self.board.update()

    def populate_chips(self):
        self.chips_list.clear()
        for k, fp in enumerate(self.fp_placed):
            x, y = fp["anchor"] % self.gw, fp["anchor"] // self.gw
            stamped = " · stamped" if fp["anchor"] in self.pins else ""
            it = QListWidgetItem(
                f"{fp['ref']}  ·  {fp['base']}  ·  {fp['rot'] * 90}°  ·  "
                f"({x},{y})  ·  {len(fp['cells'])} cells  ·  {fp['pins']} pins{stamped}")
            it.setData(Qt.UserRole, k)
            self.chips_list.addItem(it)

    def on_chip_clicked(self, item):
        k = item.data(Qt.UserRole)
        fp = self.fp_placed[k]
        if self.fp_highlight == fp["cells"]:
            self.fp_highlight = set()
        else:
            self.fp_highlight = set(fp["cells"])
        self.board.update()

    def remove_chip_stamp(self):
        it = self.chips_list.currentItem()
        if it is None:
            return
        fp = self.fp_placed[it.data(Qt.UserRole)]
        if fp["anchor"] in self.pins and self.pins[fp["anchor"]][0] == fp["base"]:
            self.push_undo()
            del self.pins[fp["anchor"]]
            self.fp_highlight = set()
            self.regen()
            self.statusBar().showMessage(f"Removed stamp {fp['ref']} ({fp['base']})", 4000)
        else:
            self.statusBar().showMessage(
                "That chip was placed by the solver, not stamped — edit weights or reseed", 4000)

    def populate_erc(self):
        self.erc_list.clear()
        nets = [n for n in self.nets if not n.internal]
        warn = 0

        def add(txt, is_warn=True):
            nonlocal warn
            if is_warn:
                warn += 1
            self.erc_list.addItem(("⚠ " if is_warn else "ℹ ") + txt)

        if not self.is_logic:
            bad_p = [n for n in nets if n.sock == 2 and not n.driven]
            bad_g = [n for n in nets if n.sock == 3 and not n.driven]
            if bad_p:
                add(f"{len(bad_p)} power net(s) with no source/battery (e.g. {bad_p[0].name})")
            if bad_g:
                add(f"{len(bad_g)} ground net(s) with no ground symbol (e.g. {bad_g[0].name})")
        else:
            bad_s = [n for n in nets if n.sock == 1 and not n.driven and len(n.cells) >= 2]
            bad_c = [n for n in nets if n.sock == 2 and not n.driven]
            if bad_s:
                add(f"{len(bad_s)} signal net(s) undriven — no VCC/GND/switch (e.g. {bad_s[0].name})")
            if bad_c:
                add(f"{len(bad_c)} clock net(s) with no clock source (e.g. {bad_c[0].name})")
        kinds_all = {self.tiles[self.model.tile_of[i]].kind
                     for i in range(self.model.n) if self.model.collapsed[i]}
        if not self.is_logic and not (kinds_all & {"source", "battery"}):
            add("Board has no power source at all")
        if self.is_logic and not (kinds_all & {"source", "clocksrc", "xtal"}):
            add("No VCC / clock sources on board")
        if self.pin_conflicts:
            add(f"{len(self.pin_conflicts)} pinned pattern(s) ignored — conflict with neighbours",
                is_warn=False)
        for a in range(len(self.fp_placed)):
            for b in range(a + 1, len(self.fp_placed)):
                A, B = self.fp_placed[a], self.fp_placed[b]
                bset = B["cells"]
                touch = False
                for i in A["cells"]:
                    x, y = i % self.gw, i // self.gw
                    for dx, dy in DIRS:
                        if (x + dx) + (y + dy) * self.gw in bset:
                            touch = True
                            break
                    if touch:
                        break
                if touch:
                    add(f"Courtyard clearance: {A['ref']} touches {B['ref']}", is_warn=False)
        open_ends = find_open_ends(self.model, self.tiles, self.gw, self.gh)
        if open_ends:
            add(f"{len(open_ends)} open trace end(s) — run Autoroute stubs", is_warn=False)
        stubs = [n for n in nets if len(n.cells) == 1]
        if stubs:
            add(f"{len(stubs)} single-pad net(s)", is_warn=False)
        if warn == 0:
            self.erc_list.addItem("✔ No issues found")

    def populate_bom(self):
        agg = {}
        m = self.model
        for i in range(m.n):
            t = self.tiles[m.tile_of[i]]
            if t.kind in NON_BOM_KINDS:
                continue
            row = agg.setdefault(t.base, [t.kind, 0, []])
            row[1] += 1
            if i in self.ref_of:
                row[2].append(self.ref_of[i])
        rows = sorted(agg.items(), key=lambda kv: (KIND_PREFIX.get(kv[1][0], "U"), -kv[1][1]))
        self.bom_table.setRowCount(len(rows))
        for r, (base, (kind, qty, refs)) in enumerate(rows):
            pfx = KIND_PREFIX.get(kind, "U")
            ref_s = f"{pfx}1–{pfx}{qty}" if qty > 1 else (refs[0] if refs else pfx + "1")
            for c, val in enumerate((ref_s, base, str(qty))):
                self.bom_table.setItem(r, c, QTableWidgetItem(val))
        self._bom_rows = rows

    def populate_stats(self):
        m = self.model
        nets = self.nets
        vias = trace = gates = comps = filled = fps = 0
        usage = defaultdict(int)
        for i in range(m.n):
            t = self.tiles[m.tile_of[i]]
            k = t.kind
            usage[t.base] += 1
            if k != "blank":
                filled += 1
            if k == "via":
                vias += 1
            elif k == "trace":
                trace += 1
            if k in COMP_KINDS:
                comps += 1
            if k in FP_ANCHOR_KINDS:
                fps += 1
            if k.startswith("gate_"):
                gates += 1
        stubs = sum(1 for n in nets if len(n.cells) == 1 and not n.internal)
        undriven = sum(1 for n in nets
                       if not n.internal and self.is_logic
                       and n.sock in (1, 2) and not n.driven)
        pub_nets = sum(1 for n in nets if not n.internal)
        s = self.stat_lbls
        s["Nets"].setText(str(pub_nets))
        s["Components"].setText(str(comps))
        s["Footprints"].setText(str(fps))
        s["Vias"].setText(str(vias))
        s["Trace cells"].setText(str(trace))
        s["Stubs"].setText(str(stubs))
        s["Gates"].setText(str(gates))
        s["Undriven nets"].setText(str(undriven))
        s["Board fill"].setText(f"{100.0 * filled / max(m.n, 1):.0f}%")
        self.usage_list.clear()
        top = sorted(usage.items(), key=lambda kv: -kv[1])[:60]
        mx = max((q for _, q in top), default=1)
        for base, qty in top:
            bar = "█" * max(1, round(18 * qty / mx))
            self.usage_list.addItem(f"{bar} {qty}  {base}")

    # ------------------------------------------------ exports

    def render_board(self, p, px):
        p.fillRect(0, 0, self.gw * px, self.gh * px, self.theme.bg)
        p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.TextAntialiasing)
        m = self.model
        for i in range(m.n):
            if m.collapsed[i]:
                p.save()
                p.translate((i % self.gw) * px, (i // self.gw) * px)
                paint_tile(p, self.tiles[m.tile_of[i]], px, self.theme)
                p.restore()

    def render_frame_img(self, tl, px):
        img = QImage(self.gw * px, self.gh * px, QImage.Format_ARGB32)
        img.fill(self.theme.bg)
        p = QPainter(img)
        p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.TextAntialiasing)
        for i, tv in enumerate(tl):
            if tv >= 0:
                p.save()
                p.translate((i % self.gw) * px, (i // self.gw) * px)
                paint_tile(p, self.tiles[tv], px, self.theme)
                p.restore()
        p.end()
        return img

    def save_png(self):
        if self.model is None:
            return
        path, _ = QFileDialog.getSaveFileName(self, "Export board as PNG",
                                              "board.png", "PNG image (*.png)")
        if not path:
            return
        px = self.cell * 4
        img = QImage(self.gw * px, self.gh * px, QImage.Format_ARGB32)
        p = QPainter(img)
        self.render_board(p, px)
        p.end()
        img.save(path)

    def save_svg(self):
        if self.model is None or not HAS_SVG:
            return
        path, _ = QFileDialog.getSaveFileName(self, "Export board as SVG",
                                              "board.svg", "SVG image (*.svg)")
        if not path:
            return
        px = 40
        gen = QSvgGenerator()
        gen.setFileName(path)
        gen.setSize(QSize(self.gw * px, self.gh * px))
        gen.setViewBox(QRect(0, 0, self.gw * px, self.gh * px))
        gen.setTitle("WFC Circuit Studio board")
        p = QPainter(gen)
        self.render_board(p, px)
        p.end()

    def export_timeline(self):
        if len(self.timeline) < 2:
            self.statusBar().showMessage("Timeline is empty — solve a board first", 4000)
            return
        path, _ = QFileDialog.getSaveFileName(self, "Export solve timeline",
                                              "wfc_timeline.gif", "Animated GIF (*.gif)")
        if not path:
            return
        px = max(8, min(24, self.cell))
        try:
            from PIL import Image  # noqa
            has_pil = True
        except ImportError:
            has_pil = False
        if has_pil:
            qimgs = [self.render_frame_img(tl, px) for tl in self.timeline]
            pils = []
            for qi in qimgs:
                buf = QBuffer()
                buf.open(QBuffer.ReadWrite)
                qi.save(buf, "PNG")
                pils.append(Image.open(io.BytesIO(bytes(buf.data()))).convert("RGB"))
            durations = [110] * len(pils)
            durations[-1] = 1200
            try:
                pils[0].save(path, save_all=True, append_images=pils[1:],
                             duration=durations, loop=0, optimize=True)
                self.statusBar().showMessage(f"GIF exported: {path} "
                                             f"({len(pils)} frames)", 6000)
            except Exception as ex:
                self.statusBar().showMessage(f"GIF export failed: {ex}", 6000)
        else:
            folder = QFileDialog.getExistingDirectory(self, "Save PNG frames to folder")
            if not folder:
                return
            for k, tl in enumerate(self.timeline):
                self.render_frame_img(tl, px).save(f"{folder}/frame_{k:03d}.png")
            self.statusBar().showMessage(
                f"Pillow not installed — exported {len(self.timeline)} PNG frames "
                f"to {folder} (pip install Pillow for direct GIF)", 6000)

    def export_csv(self):
        rows = getattr(self, "_bom_rows", None)
        if not rows:
            return
        path, _ = QFileDialog.getSaveFileName(self, "Export BOM as CSV",
                                              "bom.csv", "CSV (*.csv)")
        if not path:
            return
        with open(path, "w", encoding="utf-8") as f:
            f.write("Refs,Item,Qty\n")
            for base, (kind, qty, refs) in rows:
                rs = ";".join(refs)
                f.write(f'"{rs}","{base}",{qty}\n')

    def export_netlist(self):
        if not self.nets:
            return
        path, _ = QFileDialog.getSaveFileName(self, "Export netlist",
                                              "netlist.txt", "Text (*.txt)")
        if not path:
            return
        m = self.model

        def nname(i, s):
            nid = self.node_net.get((i, s))
            return self.nets[nid].name if nid is not None else "OPEN"

        with open(path, "w", encoding="utf-8") as f:
            f.write(f"# Netlist — WFC Circuit Studio ({self.defn.name}, seed {self.seed}, "
                    f"solver {'mcts' if self.solver_mcts else 'classic'})\n")
            f.write(f"# {sum(1 for n in self.nets if not n.internal)} nets, "
                    f"{len(self.fp_placed)} footprints, "
                    f"{len(self.ref_of)} component instances, {len(self.pins)} pins\n\n")
            for net in sorted(self.nets, key=lambda n: n.name):
                if net.internal:
                    continue
                refs = sorted({self.ref_of[i] for i in net.cells if i in self.ref_of},
                              key=lambda r: (r[0], int(''.join(filter(str.isdigit, r)) or 0)))
                f.write(f"{net.name} ({len(net.cells)} cells): "
                        f"{', '.join(refs) if refs else '(no parts)'}\n")
            if self.fp_placed:
                f.write("\n# Footprint pin map\n")
                for fp in self.fp_placed:
                    f.write(f"{fp['ref']} ({fp['base']}, {fp['rot'] * 90}°):\n")
                    for cell in sorted(fp["cells"]):
                        t = self.tiles[m.tile_of[cell]]
                        cx, cy = fp_cell(t.kind)
                        for d in range(4):
                            s = t.edges[d]
                            if s in (1, 2, 3):
                                f.write(f"  {DIRL[d]} ({cx},{cy}) -> {nname(cell, s)}\n")

    def export_verilog(self):
        if not self.nets or not self.model or not self.model.is_done():
            self.statusBar().showMessage("Solve and analyze a board first", 4000)
            return
        if not self.is_logic:
            self.statusBar().showMessage("Verilog export applies to logic-flavoured tilesets", 4000)
            return
        m = self.model

        def nname(i, s):
            nid = self.node_net.get((i, s))
            return self.nets[nid].name if nid is not None else "OPEN"

        assigns, prims, blocks, inputs, clks = [], [], [], [], []
        seen_clk = set()
        fp_by_anchor = {fp["anchor"]: fp for fp in self.fp_placed}
        for i in range(m.n):
            t = self.tiles[m.tile_of[i]]
            k = t.kind
            if k in FP_ANCHOR_KINDS:
                fp = fp_by_anchor.get(i)
                if fp:
                    pinparts = []
                    for cell in sorted(fp["cells"]):
                        tt = self.tiles[m.tile_of[cell]]
                        cx, cy = fp_cell(tt.kind)
                        for d in range(4):
                            s = tt.edges[d]
                            if s in (1, 2, 3):
                                pinparts.append(f"{DIRL[d]}({cx},{cy})={nname(cell, s)}")
                    blocks.append(f"  // {t.base} {fp['ref']}: {', '.join(pinparts)}")
                else:
                    blocks.append(f"  // {t.base} {self.ref_of.get(i, '?')} (black-box footprint)")
                continue
            if k.startswith("fp_"):
                continue
            if k in ("source", "gndsym", "switch", "clocksrc", "xtal"):
                sock = next((e for e in t.edges if e), None)
                if sock is None:
                    continue
                nm = nname(i, sock)
                if nm == "OPEN":
                    continue
                if k == "source":
                    assigns.append(f"assign {nm} = 1'b1;")
                elif k == "gndsym":
                    assigns.append(f"assign {nm} = 1'b0;")
                elif k == "switch":
                    nm_sw = f"sw{i}"
                    if nm_sw not in inputs:
                        inputs.append(nm_sw)
                    assigns.append(f"assign {nm} = {nm_sw};")
                else:
                    if nm not in seen_clk:
                        seen_clk.add(nm)
                        clks.append(f"reg {nm}_gen = 1'b0;")
                        clks.append(f"always #5 {nm}_gen = ~{nm}_gen;")
                        assigns.append(f"assign {nm} = {nm}_gen;")
                continue
            if k.startswith("gate_") and k != "gate_seg":
                o = (GATE_STYLE[k][2] + t.rot) % 4
                osock = t.edges[o]
                ins = [t.edges[d] for d in range(4) if d != o and t.edges[d]]
                if not osock or not ins:
                    continue
                prim = VERILOG_PRIM.get(k)
                oname = nname(i, osock)
                inames = [nname(i, s) for s in ins]
                if prim:
                    prims.append(f"  {prim} g{i} ({', '.join([oname] + inames)});")
                else:
                    blocks.append(f"  // {GATE_STYLE[k][0]} blk{i}: out {oname} <- "
                                  f"in {', '.join(inames)}")
            elif k == "gate_seg":
                sock = next((e for e in t.edges if e), None)
                if sock is not None:
                    blocks.append(f"  // 7-SEG dsp{i} <- {nname(i, sock)}")
        lines = ["// Structural netlist — WFC Circuit Studio (logic tileset, "
                 f"seed {self.seed})", "// Complex blocks and footprints are commented "
                 "black boxes with pin maps; wires/assigns are simulable.", "",
                 "module wfc_board("]
        port = []
        for inp in inputs:
            port.append(f"input wire {inp}")
        lines.append(",\n".join(f"    {p}" for p in port) if port else "")
        lines.append(");")
        for net in self.nets:
            if net.internal or net.name in inputs:
                continue
            lines.append(f"  wire {net.name};")
        lines.append("")
        lines.extend(f"  {c}" for c in clks)
        lines.extend(f"  {a}" for a in assigns)
        lines.append("")
        lines.extend(prims)
        if blocks:
            lines.append("")
            lines.extend(blocks)
        lines.append("endmodule")
        path, _ = QFileDialog.getSaveFileName(self, "Export Verilog netlist",
                                              "board.v", "Verilog (*.v)")
        if not path:
            return
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(lines) + "\n")
        self.statusBar().showMessage(f"Verilog exported: {path}", 5000)

    def save_project(self):
        if self.model is None:
            return
        path, _ = QFileDialog.getSaveFileName(self, "Save project",
                                              "board.json", "WFC project (*.json)")
        if not path:
            return
        data = {
            "app": "wfc-circuit-studio", "version": 5,
            "tileset": self.defn.name,
            "width": self.gw, "height": self.gh, "seed": self.seed,
            "solver": "mcts" if self.solver_mcts else "classic",
            "outline": self.outline_check.isChecked(),
            "weights": self.base_weights,
            "pins": {str(k): [b, r] for k, (b, r) in self.pins.items()},
            "zones": [list(z) for z in self.zones],
            "grid": ([self.model.tile_of[i] if self.model.collapsed[i] else -1
                      for i in range(self.model.n)]
                     if self.model.is_done() else None),
        }
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=1)
            self.statusBar().showMessage(f"Project saved: {path}", 4000)
        except OSError as ex:
            self.statusBar().showMessage(f"Save failed: {ex}", 5000)

    def open_project(self):
        path, _ = QFileDialog.getOpenFileName(self, "Open project",
                                              "", "WFC project (*.json)")
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                d = json.load(f)
        except (OSError, ValueError) as ex:
            self.statusBar().showMessage(f"Open failed: {ex}", 5000)
            return
        if d.get("app") != "wfc-circuit-studio":
            self.statusBar().showMessage("Not a WFC Circuit Studio project", 5000)
            return
        tname = d.get("tileset", "PCB board")
        if tname in self.custom_defs:
            target = tname
        elif tname in ("logic", "Logic circuit"):
            target = "Logic circuit"
        else:
            target = "PCB board"
        self.set_combo.blockSignals(True)
        self.set_combo.setCurrentText(target)
        self.set_combo.blockSignals(False)
        self.switch_tileset(self.custom_defs.get(target, BUILTIN[target]))
        merged = dict(self.defn.weights)
        merged.update(d.get("weights") or {})
        self.base_weights = merged
        self.solver_combo.blockSignals(True)
        self.solver_combo.setCurrentIndex(1 if d.get("solver") == "mcts" else 0)
        self.solver_combo.blockSignals(False)
        self.outline_check.blockSignals(True)
        self.outline_check.setChecked(bool(d.get("outline", True)))
        self.outline_check.blockSignals(False)
        self.w_spin.setValue(d.get("width", 32))
        self.h_spin.setValue(d.get("height", 32))
        self.seed_spin.setValue(d.get("seed", 0))
        pins = {}
        for k, val in (d.get("pins") or {}).items():
            if isinstance(val, (list, tuple)) and len(val) == 2:
                pins[int(k)] = (val[0], int(val[1]))
            else:
                pins[int(k)] = (str(val), 0)
        self.pins = pins
        self.zones = [tuple(z) for z in (d.get("zones") or [])]
        self.board.pixcache.clear()
        self.regen()
        grid = d.get("grid")
        if grid and len(grid) == self.model.n:
            m = self.model
            for i, tv in enumerate(grid):
                if 0 <= tv < m.T:
                    w = m.weights[tv]
                    m.mask[i] = 1 << tv
                    m.count[i] = 1
                    m.sumw[i] = w
                    m.sumwlog[i] = m.logw[tv] * w
                    m.collapsed[i] = True
                    m.tile_of[i] = tv
            m.rebuild_heap()
            self._record_timeline(force=True)
            self.was_done = True
            self.analyze()
            self.analyze_btn.setEnabled(True)
            self.reset_solver()
        self.board.update()
        self.update_stats()
        self.statusBar().showMessage(f"Project loaded: {path}", 4000)

    # ------------------------------------------------ settings

    def rebuild_layer_checks(self):
        while self.layers_box.count():
            it = self.layers_box.takeAt(0)
            if it.widget():
                it.widget().deleteLater()
        names = {1: "Signal", 2: "Power", 3: "Gnd"} if not self.is_logic \
            else {1: "Signal", 2: "Clock", 3: "Bus"}
        self.active_sockets = {1, 2, 3}
        for sid, label in names.items():
            cb = QCheckBox(label)
            cb.setChecked(True)
            cb.setFocusPolicy(Qt.NoFocus)

            def make_upd(sid, cb):
                def upd(_):
                    if cb.isChecked():
                        self.active_sockets.add(sid)
                    else:
                        self.active_sockets.discard(sid)
                    self.board.update()
                return upd

            cb.stateChanged.connect(make_upd(sid, cb))
            self.layers_box.addWidget(cb)

    def rebuild_weights_panel(self):
        self.tiles = build_tiles(self.defn, self.base_weights)
        inner = QWidget()
        v = QVBoxLayout(inner)
        v.setContentsMargins(4, 4, 4, 4)
        v.setSpacing(2)
        groups = {}
        for t in self.tiles:
            groups.setdefault(t.base, t)
        self.pin_rows = {}
        for base, t0 in groups.items():
            row = PaletteRow(base, self.on_pick_brush)
            h = QHBoxLayout(row)
            h.setContentsMargins(2, 0, 2, 0)
            h.setSpacing(6)
            icon = QLabel()
            icon.setFixedSize(30, 30)
            icon.setAlignment(Qt.AlignCenter)
            pm = QPixmap(64, 64)
            pm.fill(self.theme.bg)
            pt = QPainter(pm)
            pt.setRenderHint(QPainter.Antialiasing)
            pt.setRenderHint(QPainter.TextAntialiasing)
            if t0.kind.startswith("fp_"):
                info = FP_INFO[base]
                fw, fh = info["w"], info["h"]
                cs = max(6, 56 // max(fw, fh))
                ox = (64 - fw * cs) // 2
                oy = (64 - fh * cs) // 2
                for t in self.tiles:
                    if t.base == base and t.rot == 0:
                        ccx, ccy = fp_cell(t.kind)
                        pt.save()
                        pt.translate(ox + ccx * cs, oy + ccy * cs)
                        paint_tile(pt, t, cs, self.theme)
                        pt.restore()
            else:
                pt.scale(2, 2)
                paint_tile(pt, t0, 32, self.theme)
            pt.end()
            icon.setPixmap(pm.scaled(28, 28, Qt.KeepAspectRatio, Qt.SmoothTransformation))
            h.addWidget(icon)
            lbl = QLabel(("▣ " if base in FP_INFO else "") + base)
            lbl.setFixedWidth(104)
            h.addWidget(lbl)
            w0 = self.base_weights[base]
            sl = QSlider(Qt.Horizontal)
            sl.setRange(0, 100)
            sl.setValue(int(round(w0 * 5)))
            sl.setFocusPolicy(Qt.NoFocus)
            h.addWidget(sl, 1)
            val = QLabel(f"{w0:.1f}")
            val.setFixedWidth(30)
            h.addWidget(val)
            sl.valueChanged.connect(lambda vv, b=base, lb=val: self.on_weight(b, vv, lb))
            v.addWidget(row)
            self.pin_rows[base] = row
        v.addStretch(1)
        self.weights_scroll.setWidget(inner)

    def on_weight(self, base, v, lbl):
        w = v / 5.0
        self.base_weights[base] = w
        for t in self.tiles:
            if t.base == base:
                t.weight = w
        ws = [t.weight for t in self.tiles]
        lw = [math.log(max(x, 1e-9)) for x in ws]
        for mdl in (self.model, self.scratch):
            if mdl is not None:
                mdl.weights = ws[:]
                mdl.logw = lw[:]
                if mdl.cw:
                    mdl.set_zone_weights(self._zone_mm)
                else:
                    mdl.rebuild_heap()
        lbl.setText(f"{w:.1f}")

    def set_zoom(self, val):
        val = max(10, min(36, int(val)))
        if val == self.cell:
            return
        self.cell = val
        self.cell_slider.blockSignals(True)
        self.cell_slider.setValue(val)
        self.cell_slider.blockSignals(False)
        self.board.pixcache.clear()
        self.board.invalidate_layer()
        self.board.setFixedSize(self.gw * self.cell, self.gh * self.cell)
        self.reposition_minimap()
        self.board.update()

    def on_random_seed(self):
        self.seed_spin.setValue(random.randint(0, 999999))
        self.regen()

    def update_stats(self):
        m = self.model
        if m is None:
            return
        done = sum(m.collapsed)
        self.progress_lbl.setText(f"{done}/{m.n} ({100.0 * done / m.n:.0f}%)")
        self.restart_lbl.setText(str(self.attempt))
        if self.timeline_active():
            st = f"Timeline frame {self.timeline_pos}"
        elif self.note:
            st = self.note
        elif m.is_done():
            st = "Complete" + (" · simulating" if self.sim_active() else "")
        elif self.running:
            st = "Searching (MCTS)…" if self.solver_mcts else "Running…"
        else:
            st = "Paused"
        self.status_lbl.setText(st)


def main():
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    app.setStyleSheet(QSS)
    win = MainWindow()
    win.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()