# City & Country Economic Simulation - Expanded Edition
# Run: python simulation.py
# Requires: pygame

from __future__ import annotations

import json
import math
import os
import pickle
import random
import time
from collections import deque
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

import pygame

# ---------------------------- CONFIG ----------------------------

SCREEN_W = 1400
SCREEN_H = 700
PANEL_W = 380
MAP_W = SCREEN_W - PANEL_W
FPS = 60
TILE_SIZE = 16
GRID_W = 96
GRID_H = 64
SAVE_FILE = 'world_save.pkl'

GOODS = [
    'food', 'animals', 'wood', 'stone', 'iron', 'copper',
    'tools', 'weapons', 'cloth', 'carts', 'luxuries'
]
BASE_PRICES = {
    'food': 8.0,
    'animals': 14.0,
    'wood': 12.0,
    'stone': 9.0,
    'iron': 25.0,
    'copper': 23.0,
    'tools': 42.0,
    'weapons': 65.0,
    'cloth': 30.0,
    'carts': 58.0,
    'luxuries': 90.0,
}
SPECIALIZATIONS = ['farming', 'herding', 'logging', 'mining', 'smithing', 'weaving', 'cartwright', 'merchant']

BIOME_COLORS = {
    'water': (28, 72, 132),
    'desert': (196, 182, 108),
    'plains': (84, 148, 76),
    'forest': (34, 108, 54),
    'hills': (116, 116, 96),
    'mountain': (146, 146, 154),
}

# ---------------------------- HELPERS ----------------------------

def clamp(v, lo, hi):
    return max(lo, min(hi, v))


def lerp(a, b, t):
    return a + (b - a) * t


def dist(ax, ay, bx, by):
    return math.hypot(ax - bx, ay - by)


def bright_color(rng: random.Random) -> Tuple[int, int, int]:
    h = rng.random()
    s = 0.55 + rng.random() * 0.35
    v = 0.75 + rng.random() * 0.2
    import colorsys
    r, g, b = colorsys.hsv_to_rgb(h, s, v)
    return (int(r * 255), int(g * 255), int(b * 255))


def avg(vals):
    return sum(vals) / len(vals) if vals else 0


def smooth_noise(grid, passes=3):
    h = len(grid)
    w = len(grid[0])
    for _ in range(passes):
        nxt = [[0.0 for _ in range(w)] for _ in range(h)]
        for y in range(h):
            for x in range(w):
                total = 0.0
                count = 0
                for yy in range(max(0, y - 1), min(h, y + 2)):
                    for xx in range(max(0, x - 1), min(w, x + 2)):
                        total += grid[yy][xx]
                        count += 1
                nxt[y][x] = total / count
        grid = nxt
    return grid


# ---------------------------- DATA ----------------------------

@dataclass
class Tile:
    biome: str
    height: float
    moisture: float
    fertility: float
    owner: int = -1
    resources: Dict[str, float] = field(default_factory=dict)


class Market:
    def __init__(self):
        self.prices = dict(BASE_PRICES)
        self.history = {g: deque(maxlen=160) for g in GOODS}

    def update(self, supply: Dict[str, float], demand: Dict[str, float]):
        for g in GOODS:
            s = max(0.0, supply.get(g, 0.0))
            d = max(0.0, demand.get(g, 0.0))
            base = BASE_PRICES[g]
            imbalance = (d - s) / max(1.0, d + s)
            scarcity = 1.0 + (0.9 if s < d * 0.35 else 0.0)
            price = base * (1.0 + imbalance * 0.95) * scarcity
            self.prices[g] = clamp(price, base * 0.25, base * 9.0)
            self.history[g].append(self.prices[g])


class Country:
    def __init__(self, cid: int, name: str, color: Tuple[int, int, int]):
        self.id = cid
        self.name = name
        self.color = color
        self.cities: List[City] = []
        self.villages: List[Village] = []
        self.relations: Dict[str, float] = {}
        self.at_war: set[str] = set()
        self.treasury = 0.0
        self.tax_rate = 0.045
        self.war_exhaustion = 0.0

    def strength(self):
        pop = sum(c.population for c in self.cities)
        wealth = sum(c.wealth for c in self.cities)
        weapons = sum(c.stock.get('weapons', 0.0) for c in self.cities)
        return pop * 1.2 + wealth * 0.08 + weapons * 10.0

    def economy_score(self):
        return sum(c.wealth for c in self.cities) + sum(c.population for c in self.cities) * 4.0 + self.treasury

    def relation(self, other_name: str):
        return self.relations.get(other_name, 0.0)


class City:
    def __init__(self, cid: int, name: str, x: float, y: float, country: Country, tile: Tile, size_class: str, rng: random.Random):
        self.id = cid
        self.name = name
        self.x = x
        self.y = y
        self.country = country
        self.tile = tile
        self.size_class = size_class
        self.specialization = rng.choice(SPECIALIZATIONS)
        self.population = {'small': rng.randint(700, 1800), 'medium': rng.randint(1800, 5200), 'large': rng.randint(5200, 14000)}[size_class]
        self.wealth = rng.randint(1200, 8000) + (2000 if size_class == 'large' else 0)
        self.stock = {g: 0.0 for g in GOODS}
        self.stock.update({
            'food': rng.randint(80, 240),
            'animals': rng.randint(20, 100),
            'wood': rng.randint(50, 200),
            'stone': rng.randint(20, 120),
            'iron': rng.randint(10, 90),
            'copper': rng.randint(8, 60),
            'tools': rng.randint(5, 50),
            'weapons': rng.randint(2, 30),
            'cloth': rng.randint(15, 90),
            'carts': rng.randint(0, 18),
            'luxuries': rng.randint(0, 20),
        })
        self.market = Market()
        self.villages: List[Village] = []
        self.routes: List[TradeRoute] = []
        self.effects: List[dict] = []
        self.population_history = deque(maxlen=180)
        self.wealth_history = deque(maxlen=180)
        self.last_report = ''

    def add_effect(self, name, ttl, prod=1.0, growth=1.0, cons=1.0, wealth=0.0, pop=0.0):
        self.effects.append({'name': name, 'ttl': ttl, 'prod': prod, 'growth': growth, 'cons': cons})
        self.wealth += wealth
        self.population = max(10.0, self.population + pop)
        self.last_report = name

    def effect_multipliers(self):
        prod = 1.0
        growth = 1.0
        cons = 1.0
        for e in self.effects:
            prod *= e['prod']
            growth *= e['growth']
            cons *= e['cons']
        return prod, growth, cons

    def decay_effects(self):
        kept = []
        for e in self.effects:
            e['ttl'] -= 1
            if e['ttl'] > 0:
                kept.append(e)
        self.effects = kept

    def demand(self):
        p = self.population
        d = {g: 0.0 for g in GOODS}
        d['food'] = p * 0.9
        d['cloth'] = p * 0.12
        d['tools'] = p * 0.06
        d['carts'] = p * 0.01
        d['luxuries'] = p * 0.02
        if self.country.at_war:
            d['weapons'] = p * 0.03
        return d

    def produce_raw(self, prod_mult=1.0):
        t = self.tile
        workforce = self.population * 0.28
        local_boost = 0.6 + t.fertility * 0.8
        if t.biome == 'forest':
            local_boost += 0.2
        if t.biome == 'mountain':
            local_boost += 0.1

        # universal extraction from the local tile
        self.stock['food'] += workforce * 0.05 * t.fertility * prod_mult
        self.stock['animals'] += workforce * 0.02 * clamp(t.fertility + 0.2, 0, 1) * prod_mult
        self.stock['wood'] += workforce * 0.04 * t.resources.get('wood', 0.2) * prod_mult
        self.stock['stone'] += workforce * 0.03 * t.resources.get('stone', 0.2) * prod_mult
        self.stock['iron'] += workforce * 0.018 * t.resources.get('iron', 0.15) * prod_mult
        self.stock['copper'] += workforce * 0.014 * t.resources.get('copper', 0.12) * prod_mult
        self.stock['cloth'] += workforce * 0.01 * (t.fertility + 0.2) * prod_mult

        # specialization-driven manufacturing
        if self.specialization == 'farming':
            self.stock['food'] += workforce * 0.12 * local_boost * prod_mult
        elif self.specialization == 'herding':
            self.stock['animals'] += workforce * 0.08 * local_boost * prod_mult
            self.stock['food'] += workforce * 0.03 * local_boost * prod_mult
        elif self.specialization == 'logging':
            self.stock['wood'] += workforce * 0.12 * local_boost * prod_mult
        elif self.specialization == 'mining':
            self.stock['iron'] += workforce * 0.05 * (t.resources.get('iron', 0.2) + 0.2) * prod_mult
            self.stock['copper'] += workforce * 0.04 * (t.resources.get('copper', 0.2) + 0.2) * prod_mult
            self.stock['stone'] += workforce * 0.08 * (t.resources.get('stone', 0.2) + 0.2) * prod_mult
        elif self.specialization == 'smithing':
            ore = min(self.stock['iron'] * 0.55, self.stock['wood'] * 0.6, workforce * 0.22)
            self.stock['iron'] -= ore * 0.55
            self.stock['wood'] -= ore * 0.60
            self.stock['tools'] += ore * 1.7 * prod_mult
            self.stock['weapons'] += ore * 0.9 * prod_mult
            self.stock['carts'] += ore * 0.4 * prod_mult
        elif self.specialization == 'weaving':
            fiber = min(self.stock['animals'] * 0.4, workforce * 0.25)
            self.stock['animals'] -= fiber * 0.3
            self.stock['cloth'] += fiber * 1.9 * prod_mult
            self.stock['luxuries'] += fiber * 0.22 * prod_mult
        elif self.specialization == 'cartwright':
            mats = min(self.stock['wood'] * 0.45, self.stock['iron'] * 0.25, workforce * 0.18)
            self.stock['wood'] -= mats * 0.45
            self.stock['iron'] -= mats * 0.25
            self.stock['carts'] += mats * 1.5 * prod_mult
            self.stock['tools'] += mats * 0.55 * prod_mult
        elif self.specialization == 'merchant':
            self.stock['luxuries'] += workforce * 0.06 * prod_mult
            self.stock['tools'] += workforce * 0.02 * prod_mult

    def consume(self, growth_mult=1.0, cons_mult=1.0):
        food_need = self.population * 0.085 * cons_mult
        food_used = min(self.stock['food'], food_need)
        self.stock['food'] -= food_used

        shortage = max(0.0, food_need - food_used) / max(1.0, food_need)
        luxury_bonus = min(self.stock['luxuries'] / max(1.0, self.population * 0.12), 0.25)
        wealth_factor = clamp(self.wealth / max(1.0, self.population * 9.0), 0.0, 2.0)

        if shortage > 0.0:
            self.population *= clamp(1.0 - shortage * 0.18, 0.90, 0.995)
            self.wealth *= clamp(1.0 - shortage * 0.10, 0.93, 1.0)
        else:
            growth = 1.0 + 0.006 * growth_mult + luxury_bonus * 0.004 + wealth_factor * 0.0015
            if self.country.at_war:
                growth -= 0.004
            self.population *= clamp(growth, 0.98, 1.03)
            self.wealth += (food_used * 0.02) + (luxury_bonus * 4.0)

        # old goods rot or get consumed by the local economy
        for g in ('food', 'animals', 'cloth', 'luxuries'):
            self.stock[g] = max(0.0, self.stock[g] * 0.985)
        self.population = clamp(self.population, 50.0, 200000.0)
        self.wealth = clamp(self.wealth, 0.0, 10**9)

    def tax_and_record(self):
        tax = self.wealth * self.country.tax_rate * 0.01
        self.wealth -= tax
        self.country.treasury += tax
        self.population_history.append(self.population)
        self.wealth_history.append(self.wealth)

    def update_market(self):
        demand = self.demand()
        supply = {g: self.stock.get(g, 0.0) for g in GOODS}
        self.market.update(supply, demand)

    def post_trade_valuation(self):
        # Convert stock into a lightweight wealth signal so production matters even before trade.
        value = 0.0
        for g in GOODS:
            value += self.stock[g] * self.market.prices[g] * 0.0012
        self.wealth += value * 0.01

    def step(self, world):
        prod_mult, growth_mult, cons_mult = self.effect_multipliers()
        self.produce_raw(prod_mult)
        self.update_market()
        self.consume(growth_mult, cons_mult)
        self.post_trade_valuation()
        self.tax_and_record()
        self.decay_effects()

    def visual_radius(self):
        if self.size_class == 'small':
            return 4 + int(math.log(max(10.0, self.population), 10))
        if self.size_class == 'medium':
            return 6 + int(math.log(max(10.0, self.population), 10))
        return 8 + int(math.log(max(10.0, self.population), 10))


class Village:
    def __init__(self, vid: int, name: str, x: float, y: float, country: Country, tile: Tile, home_city: City, rng: random.Random):
        self.id = vid
        self.name = name
        self.x = x
        self.y = y
        self.country = country
        self.tile = tile
        self.home_city = home_city
        self.population = rng.randint(120, 1100)
        self.wealth = rng.randint(80, 500)
        self.stock = {g: 0.0 for g in GOODS}
        self.stock.update({'food': rng.randint(20, 80), 'animals': rng.randint(5, 25), 'wood': rng.randint(5, 40), 'stone': rng.randint(0, 12)})
        self.route: Optional[TradeRoute] = None
        self.population_history = deque(maxlen=180)
        self.wealth_history = deque(maxlen=180)

    def produce(self):
        t = self.tile
        workforce = self.population * 0.24
        self.stock['food'] += workforce * 0.09 * (0.6 + t.fertility)
        self.stock['animals'] += workforce * 0.02 * (0.4 + t.fertility)
        self.stock['wood'] += workforce * 0.015 * t.resources.get('wood', 0.2)
        self.stock['stone'] += workforce * 0.007 * t.resources.get('stone', 0.2)
        self.stock['cloth'] += workforce * 0.004 * t.fertility

    def consume(self):
        need = self.population * 0.06
        used = min(self.stock['food'], need)
        self.stock['food'] -= used
        if used < need:
            self.population *= 0.985
        else:
            self.population *= 1.004
        self.population = clamp(self.population, 40.0, 6000.0)
        self.wealth += used * 0.01
        self.wealth = clamp(self.wealth, 0.0, 100000.0)

    def step(self, world):
        self.produce()
        self.consume()
        self.population_history.append(self.population)
        self.wealth_history.append(self.wealth)

    def visual_radius(self):
        return 2


class TradeRoute:
    def __init__(self, a, b, kind='trade'):
        self.a = a
        self.b = b
        self.kind = kind  # 'trade' or 'supply'
        self.active = True
        self.last_flow = ''

    def distance(self):
        return dist(self.a.x, self.a.y, self.b.x, self.b.y)

    def blocked_by_war(self):
        ca = self.a.country.name
        cb = self.b.country.name
        return ca != cb and (cb in self.a.country.at_war or ca in self.b.country.at_war)

    def tick(self, world):
        self.active = True
        self.last_flow = ''
        if self.kind == 'supply':
            self._supply_tick(world)
        else:
            self._trade_tick(world)

    def _supply_tick(self, world):
        source = self.a
        sink = self.b
        cap = 30.0 + 50.0 / (1.0 + self.distance() / 130.0)
        if self.blocked_by_war():
            cap *= 0.15
            self.active = False
        moved = 0.0
        for g in ('food', 'animals', 'wood', 'stone', 'cloth'):
            target = source.population * (0.12 if g == 'food' else 0.03)
            surplus = max(0.0, source.stock.get(g, 0.0) - target)
            amt = min(surplus, cap * (0.6 if g == 'food' else 0.25))
            if amt > 0:
                source.stock[g] -= amt
                sink.stock[g] = sink.stock.get(g, 0.0) + amt
                moved += amt
        if moved > 0:
            source.wealth += moved * 0.02
            sink.wealth = max(0.0, sink.wealth - moved * 0.01)
            self.last_flow = f'{source.name} -> {sink.name} ({moved:.1f})'

    def _trade_tick(self, world):
        a = self.a
        b = self.b
        cap = 45.0 + 80.0 / (1.0 + self.distance() / 160.0)
        if self.blocked_by_war():
            cap *= 0.08
            self.active = False
        trade_bonus = 1.0
        if a.country.name != b.country.name and b.country.name not in a.country.at_war:
            trade_bonus = 1.15
        best = []
        for g in GOODS:
            pa = a.market.prices[g]
            pb = b.market.prices[g]
            spread = abs(pa - pb)
            if spread > BASE_PRICES[g] * 0.12:
                best.append((spread, g, pa, pb))
        best.sort(reverse=True)
        total = 0.0
        for _, g, pa, pb in best[:3]:
            if pa > pb:
                source, sink = b, a
                price_gap = pa - pb
            else:
                source, sink = a, b
                price_gap = pb - pa
            transport_cost = self.distance() * 0.018
            if price_gap <= transport_cost:
                continue
            demand_gap = max(0.0, sink.market.prices[g] / BASE_PRICES[g] - 0.2)
            amt = min(source.stock.get(g, 0.0), cap * trade_bonus * (0.35 + demand_gap), 100.0)
            if amt <= 0:
                continue
            source.stock[g] -= amt
            sink.stock[g] = sink.stock.get(g, 0.0) + amt
            source.wealth += amt * source.market.prices[g] * 0.02
            sink.wealth -= amt * sink.market.prices[g] * 0.01
            total += amt
            self.last_flow = f'{source.name} -> {sink.name}: {g} {amt:.1f}'
        if total > 0 and a.country.name != b.country.name:
            a.country.relations[b.country.name] = clamp(a.country.relations.get(b.country.name, 0.0) + 0.12 * total, -100.0, 100.0)
            b.country.relations[a.country.name] = clamp(b.country.relations.get(a.country.name, 0.0) + 0.12 * total, -100.0, 100.0)

    def draw(self, surface, camera):
        ca = self.a.country.color if hasattr(self.a, 'country') else (200, 200, 200)
        cb = self.b.country.color if hasattr(self.b, 'country') else (200, 200, 200)
        if self.kind == 'supply':
            color = (190, 180, 100)
            width = 2
        else:
            color = tuple(int((ca[i] + cb[i]) * 0.5) for i in range(3))
            width = 1 if self.active else 1
        if self.blocked_by_war():
            color = (170, 60, 60)
        p1 = camera.world_to_screen(self.a.x, self.a.y)
        p2 = camera.world_to_screen(self.b.x, self.b.y)
        pygame.draw.line(surface, color, p1, p2, width)


# ---------------------------- WORLD ----------------------------

class World:
    def __init__(self, seed: Optional[int] = None):
        self.seed = seed if seed is not None else int(time.time())
        self.rng = random.Random(self.seed)
        self.tick = 0
        self.tiles: List[List[Tile]] = []
        self.countries: List[Country] = []
        self.cities: List[City] = []
        self.villages: List[Village] = []
        self.routes: List[TradeRoute] = []
        self.log = deque(maxlen=80)
        self.population_history = deque(maxlen=240)
        self.price_history = deque(maxlen=240)
        self.gdp_history = deque(maxlen=240)
        self.generate()

    # -------- generation --------

    def generate(self):
        self._generate_tiles()
        self._generate_countries()
        self._place_cities_and_villages()
        self._generate_routes()
        self.log_event(f'World generated with seed {self.seed}')

    def _generate_tiles(self):
        rng = self.rng
        h0 = smooth_noise([[rng.random() for _ in range(GRID_W)] for _ in range(GRID_H)], 4)
        m0 = smooth_noise([[rng.random() for _ in range(GRID_W)] for _ in range(GRID_H)], 4)
        self.tiles = []
        for y in range(GRID_H):
            row = []
            lat = abs((y / (GRID_H - 1)) - 0.5) * 2.0
            for x in range(GRID_W):
                height = clamp(h0[y][x] * 0.75 + (1.0 - lat) * 0.18, 0.0, 1.0)
                moisture = clamp(m0[y][x] * 0.8 + rng.random() * 0.2, 0.0, 1.0)
                fertility = clamp(0.15 + moisture * 0.65 - abs(height - 0.38) * 0.35, 0.0, 1.0)
                if height < 0.23:
                    biome = 'water'
                elif height > 0.8:
                    biome = 'mountain'
                elif moisture < 0.24:
                    biome = 'desert'
                elif fertility > 0.62:
                    biome = 'plains'
                elif moisture > 0.62:
                    biome = 'forest'
                else:
                    biome = 'hills'
                resources = {
                    'wood': 0.0,
                    'stone': 0.0,
                    'iron': 0.0,
                    'copper': 0.0,
                }
                if biome == 'forest':
                    resources['wood'] = 0.7 + rng.random() * 0.8
                elif biome == 'plains':
                    resources['wood'] = 0.25 + rng.random() * 0.3
                elif biome == 'hills':
                    resources['stone'] = 0.45 + rng.random() * 0.5
                    resources['iron'] = 0.18 + rng.random() * 0.35
                elif biome == 'mountain':
                    resources['stone'] = 0.8 + rng.random() * 0.8
                    resources['iron'] = 0.35 + rng.random() * 0.75
                    resources['copper'] = 0.18 + rng.random() * 0.5
                elif biome == 'desert':
                    resources['stone'] = 0.35 + rng.random() * 0.25
                if rng.random() < 0.04 and biome not in ('water', 'desert'):
                    resources['copper'] += 0.4 + rng.random() * 0.5
                row.append(Tile(biome, height, moisture, fertility, -1, resources))
            self.tiles.append(row)

    def _generate_countries(self):
        rng = self.rng
        country_count = rng.randint(4, 6)
        seeds = []
        for i in range(country_count):
            while True:
                x = rng.randint(6, GRID_W - 7)
                y = rng.randint(6, GRID_H - 7)
                if self.tiles[y][x].biome != 'water':
                    seeds.append((x, y))
                    break
        self.countries = [Country(i, f'Country {i + 1}', bright_color(rng)) for i in range(country_count)]
        for y in range(GRID_H):
            for x in range(GRID_W):
                if self.tiles[y][x].biome == 'water':
                    continue
                best = None
                best_d = 10**9
                for i, (sx, sy) in enumerate(seeds):
                    d = (sx - x) ** 2 + (sy - y) ** 2
                    if d < best_d:
                        best_d = d
                        best = i
                self.tiles[y][x].owner = best

        # seed relations
        for c in self.countries:
            for other in self.countries:
                if other.name != c.name:
                    c.relations[other.name] = rng.uniform(-8, 18)

    def _country_tiles(self, cid):
        for y in range(GRID_H):
            for x in range(GRID_W):
                if self.tiles[y][x].owner == cid:
                    yield x, y, self.tiles[y][x]

    def _score_tile_for_city(self, tile: Tile, x: int, y: int, country: Country):
        if tile.biome == 'water':
            return -999
        score = tile.fertility * 1.2
        score += tile.resources.get('wood', 0.0) * 0.25
        score += tile.resources.get('iron', 0.0) * 0.3
        score += tile.resources.get('copper', 0.0) * 0.25
        score += 0.15 if tile.biome == 'plains' else 0.0
        score += 0.1 if tile.biome == 'forest' else 0.0
        score += 0.08 if tile.biome == 'hills' else 0.0
        # keep cities a bit apart
        for c in self.cities:
            if c.country == country:
                d = dist(c.x / TILE_SIZE, c.y / TILE_SIZE, x, y)
                score -= max(0.0, 2.0 - d / 8.0)
        return score

    def _choose_specialization(self, tile: Tile):
        if tile.fertility > 0.68:
            return self.rng.choice(['farming', 'farming', 'merchant', 'herding'])
        if tile.resources.get('iron', 0) > 0.6 or tile.resources.get('copper', 0) > 0.45:
            return self.rng.choice(['mining', 'smithing', 'cartwright'])
        if tile.resources.get('wood', 0) > 0.6:
            return self.rng.choice(['logging', 'weaving', 'merchant'])
        return self.rng.choice(SPECIALIZATIONS)

    def _place_cities_and_villages(self):
        rng = self.rng
        cid = 0
        vid = 0
        city_id = 0
        for country in self.countries:
            tiles = list(self._country_tiles(country.id))
            tiles.sort(key=lambda item: self._score_tile_for_city(item[2], item[0], item[1], country), reverse=True)
            city_count = clamp(3 + len(tiles) // 600, 3, 7)
            chosen: List[Tuple[int, int, Tile]] = []
            for x, y, tile in tiles:
                if tile.biome == 'water':
                    continue
                if any(abs(x - ox) + abs(y - oy) < 9 for ox, oy, _ in chosen):
                    continue
                chosen.append((x, y, tile))
                if len(chosen) >= int(city_count):
                    break
            if not chosen:
                continue
            for idx, (x, y, tile) in enumerate(chosen):
                size_class = 'large' if idx == 0 else ('medium' if idx < 3 else 'small')
                name = f'{country.name} City {idx + 1}'
                city = City(city_id, name, (x + 0.5) * TILE_SIZE, (y + 0.5) * TILE_SIZE, country, tile, size_class, rng)
                city.specialization = self._choose_specialization(tile)
                country.cities.append(city)
                self.cities.append(city)
                city_id += 1

        # villages around cities
        for city in self.cities:
            desired = rng.randint(2, 6)
            placed = 0
            tries = 0
            while placed < desired and tries < 40:
                tries += 1
                ox = rng.randint(-6, 6)
                oy = rng.randint(-6, 6)
                tx = int(city.x / TILE_SIZE) + ox
                ty = int(city.y / TILE_SIZE) + oy
                if not (0 <= tx < GRID_W and 0 <= ty < GRID_H):
                    continue
                tile = self.tiles[ty][tx]
                if tile.biome == 'water' or tile.owner != city.country.id:
                    continue
                if any(dist((tx + 0.5) * TILE_SIZE, (ty + 0.5) * TILE_SIZE, v.x, v.y) < 48 for v in self.villages):
                    continue
                v = Village(vid, f'{city.name} Village {placed + 1}', (tx + 0.5) * TILE_SIZE, (ty + 0.5) * TILE_SIZE, city.country, tile, city, rng)
                self.villages.append(v)
                city.country.villages.append(v)
                city.villages.append(v)
                vid += 1
                placed += 1

    def _route_exists(self, a, b):
        for r in self.routes:
            if (r.a == a and r.b == b) or (r.a == b and r.b == a):
                return True
        return False

    def _generate_routes(self):
        rng = self.rng
        # village -> home city supply lines
        for v in self.villages:
            route = TradeRoute(v, v.home_city, kind='supply')
            self.routes.append(route)
            v.route = route

        # city-city trade network: near neighbors + some international links
        for city in self.cities:
            others = [c for c in self.cities if c != city]
            others.sort(key=lambda c: dist(city.x, city.y, c.x, c.y))
            same = [c for c in others if c.country == city.country][:2]
            foreign = [c for c in others if c.country != city.country][:1]
            for other in same + foreign:
                if not self._route_exists(city, other):
                    self.routes.append(TradeRoute(city, other, kind='trade'))

    # -------- gameplay --------

    def log_event(self, msg: str):
        self.log.appendleft(f'[{self.tick}] {msg}')

    def tile_at(self, px, py):
        gx = clamp(int(px // TILE_SIZE), 0, GRID_W - 1)
        gy = clamp(int(py // TILE_SIZE), 0, GRID_H - 1)
        return self.tiles[gy][gx]

    def total_population(self):
        return sum(c.population for c in self.cities) + sum(v.population for v in self.villages)

    def total_wealth(self):
        return sum(c.wealth for c in self.cities) + sum(v.wealth for v in self.villages) + sum(country.treasury for country in self.countries)

    def average_price(self):
        all_prices = [c.market.prices[g] for c in self.cities for g in GOODS]
        return avg(all_prices)

    def country_by_name(self, name: str):
        for c in self.countries:
            if c.name == name:
                return c
        return None

    def city_by_name(self, name: str):
        for c in self.cities:
            if c.name == name:
                return c
        return None

    def step_diplomacy_and_war(self):
        rng = self.rng
        # relations drift and occasional wars
        for c in self.countries:
            c.war_exhaustion = clamp(c.war_exhaustion * 0.995, 0.0, 100.0)
            for other_name in list(c.relations.keys()):
                rel = c.relations[other_name]
                trade_factor = 0.0
                for r in self.routes:
                    if r.kind != 'trade':
                        continue
                    if r.a.country.name == c.name and r.b.country.name == other_name:
                        trade_factor += 0.02
                    elif r.b.country.name == c.name and r.a.country.name == other_name:
                        trade_factor += 0.02
                rel = clamp(rel + trade_factor - 0.01 * len(c.at_war), -100.0, 100.0)
                c.relations[other_name] = rel
                if other_name in c.at_war:
                    if rel > -10 and rng.random() < 0.01:
                        c.at_war.remove(other_name)
                        other = self.country_by_name(other_name)
                        if other:
                            other.at_war.discard(c.name)
                        self.log_event(f'Peace treaty between {c.name} and {other_name}')
                else:
                    if rel < -50 and rng.random() < 0.02:
                        c.at_war.add(other_name)
                        other = self.country_by_name(other_name)
                        if other:
                            other.at_war.add(c.name)
                        self.log_event(f'War breaks out between {c.name} and {other_name}')

        # war attrition
        for c in self.countries:
            if c.at_war:
                c.war_exhaustion += 0.25
                c.treasury -= 2.0 * len(c.at_war)
                for city in c.cities:
                    city.population *= 0.999
                    city.wealth *= 0.999

    def step_events(self):
        rng = self.rng
        if self.tick % 22 != 0:
            return
        if rng.random() < 0.65:
            return
        roll = rng.random()
        city = rng.choice(self.cities)
        country = city.country
        if roll < 0.20:
            city.add_effect('Famine', 18, prod=0.82, growth=0.90, cons=1.0)
            city.stock['food'] *= 0.7
            self.log_event(f'Famine hits {city.name}')
        elif roll < 0.40:
            city.add_effect('Boom', 16, prod=1.18, growth=1.05, cons=0.95, wealth=200 + rng.randint(0, 400))
            self.log_event(f'Economic boom in {city.name}')
        elif roll < 0.60:
            city.stock['iron'] += 90 + rng.randint(0, 140)
            city.stock['copper'] += 40 + rng.randint(0, 80)
            self.log_event(f'Resource discovery near {city.name}')
        elif roll < 0.80:
            loss = city.population * (0.03 + rng.random() * 0.05)
            city.population -= loss
            city.add_effect('Plague', 10, prod=0.90, growth=0.82, cons=1.05)
            self.log_event(f'Plague spreads in {city.name}')
        else:
            burned = min(city.wealth * 0.18, 1200)
            city.wealth -= burned
            for g in ('food', 'tools', 'cloth', 'luxuries'):
                city.stock[g] *= 0.85
            city.add_effect('Fire', 8, prod=0.88, growth=0.96, cons=1.02)
            self.log_event(f'Fire damages {city.name}')

    def migration(self):
        # Simple local migration: people drift toward the most prosperous city in their country.
        for country in self.countries:
            if len(country.cities) < 2:
                continue
            best = max(country.cities, key=lambda c: (c.wealth / max(1.0, c.population)) + c.market.prices['food'] * 0.0)
            worst = min(country.cities, key=lambda c: (c.wealth / max(1.0, c.population)) + c.population * 0.0)
            if best == worst:
                continue
            gap = (best.wealth / max(1.0, best.population)) - (worst.wealth / max(1.0, worst.population))
            if gap > 0.5 and worst.population > 250:
                migrants = min(worst.population * 0.01, gap * 5.0)
                worst.population -= migrants
                best.population += migrants * 0.92
                best.wealth += migrants * 0.4
                worst.wealth *= 0.999
                self.log_event(f'Migration from {worst.name} to {best.name}')

    def step(self):
        self.tick += 1
        self.step_diplomacy_and_war()

        for v in self.villages:
            v.step(self)
        for c in self.cities:
            c.step(self)

        # update markets after production/consumption
        for c in self.cities:
            c.update_market()

        for r in self.routes:
            r.tick(self)

        self.migration()
        self.step_events()

        self.population_history.append(self.total_population())
        self.price_history.append(self.average_price())
        self.gdp_history.append(self.total_wealth())

        # record world summaries
        if self.tick % 10 == 0:
            richest = max(self.cities, key=lambda c: c.wealth)
            self.log_event(f'Tick {self.tick}: population {int(self.total_population())}, richest {richest.name}')

    # -------- persistence --------

    def save(self, path=SAVE_FILE):
        with open(path, 'wb') as f:
            pickle.dump(self, f, protocol=pickle.HIGHEST_PROTOCOL)
        self.log_event(f'Saved to {path}')

    @staticmethod
    def load(path=SAVE_FILE):
        with open(path, 'rb') as f:
            world = pickle.load(f)
        return world

    # -------- rendering --------

    def draw_tiles(self, surface, camera):
        start_x, start_y, end_x, end_y = camera.visible_tile_bounds()
        tile_px = TILE_SIZE * camera.zoom
        for gy in range(start_y, end_y):
            for gx in range(start_x, end_x):
                t = self.tiles[gy][gx]
                color = BIOME_COLORS[t.biome]
                if t.biome != 'water' and t.owner >= 0:
                    owner = self.countries[t.owner].color
                    mix = 0.22 if t.biome in ('plains', 'forest') else 0.12
                    color = tuple(int(color[i] * (1 - mix) + owner[i] * mix) for i in range(3))
                rect = pygame.Rect(
                    int((gx * TILE_SIZE - camera.x) * camera.zoom),
                    int((gy * TILE_SIZE - camera.y) * camera.zoom),
                    max(1, int(tile_px) + 1),
                    max(1, int(tile_px) + 1),
                )
                pygame.draw.rect(surface, color, rect)

    def draw_routes(self, surface, camera):
        for r in self.routes:
            r.draw(surface, camera)

    def draw_nodes(self, surface, camera, selected_city=None):
        for v in self.villages:
            p = camera.world_to_screen(v.x, v.y)
            if 0 <= p[0] <= MAP_W and 0 <= p[1] <= SCREEN_H:
                pygame.draw.circle(surface, (225, 225, 225), p, max(1, int(2 * camera.zoom)))
        for c in self.cities:
            p = camera.world_to_screen(c.x, c.y)
            if 0 <= p[0] <= MAP_W and 0 <= p[1] <= SCREEN_H:
                radius = max(3, int(c.visual_radius() * camera.zoom))
                pygame.draw.circle(surface, c.country.color, p, radius)
                if c == selected_city:
                    pygame.draw.circle(surface, (255, 255, 255), p, radius + 4, 2)

    def draw_world(self, surface, camera, selected_city=None):
        self.draw_tiles(surface, camera)
        self.draw_routes(surface, camera)
        self.draw_nodes(surface, camera, selected_city)


# ---------------------------- CAMERA ----------------------------

class Camera:
    def __init__(self):
        self.x = 0.0
        self.y = 0.0
        self.zoom = 1.0
        self.dragging = False
        self.drag_anchor = (0, 0)
        self.pan_anchor = (0.0, 0.0)

    def world_to_screen(self, wx, wy):
        sx = int((wx - self.x) * self.zoom)
        sy = int((wy - self.y) * self.zoom)
        return sx, sy

    def screen_to_world(self, sx, sy):
        return sx / self.zoom + self.x, sy / self.zoom + self.y

    def visible_tile_bounds(self):
        tile_px = TILE_SIZE * self.zoom
        start_x = clamp(int(self.x // TILE_SIZE) - 2, 0, GRID_W - 1)
        start_y = clamp(int(self.y // TILE_SIZE) - 2, 0, GRID_H - 1)
        end_x = clamp(int((self.x + MAP_W / self.zoom) // TILE_SIZE) + 3, 0, GRID_W)
        end_y = clamp(int((self.y + SCREEN_H / self.zoom) // TILE_SIZE) + 3, 0, GRID_H)
        return start_x, start_y, end_x, end_y

    def zoom_at(self, mx, my, amount):
        before = self.screen_to_world(mx, my)
        self.zoom = clamp(self.zoom * amount, 0.55, 2.8)
        after = self.screen_to_world(mx, my)
        self.x += before[0] - after[0]
        self.y += before[1] - after[1]
        self.clamp_to_world()

    def clamp_to_world(self):
        max_x = GRID_W * TILE_SIZE - MAP_W / self.zoom
        max_y = GRID_H * TILE_SIZE - SCREEN_H / self.zoom
        self.x = clamp(self.x, 0, max(0, max_x))
        self.y = clamp(self.y, 0, max(0, max_y))


# ---------------------------- UI ----------------------------

def draw_text(surface, font, text, x, y, color=(235, 235, 235)):
    surface.blit(font.render(text, True, color), (x, y))


def draw_bar(surface, x, y, w, h, frac, fg, bg=(50, 50, 60)):
    pygame.draw.rect(surface, bg, (x, y, w, h), border_radius=5)
    pygame.draw.rect(surface, fg, (x, y, int(w * clamp(frac, 0.0, 1.0)), h), border_radius=5)


def draw_graph(surface, rect, values, color, title='', font=None):
    pygame.draw.rect(surface, (26, 28, 38), rect, border_radius=8)
    pygame.draw.rect(surface, (80, 86, 102), rect, 1, border_radius=8)
    if font and title:
        draw_text(surface, font, title, rect.x + 8, rect.y + 6, (210, 210, 220))
    if len(values) < 2:
        return
    inner = rect.inflate(-16, -24)
    inner.y += 16
    mn = min(values)
    mx = max(values)
    if abs(mx - mn) < 1e-9:
        mx = mn + 1.0
    pts = []
    for i, v in enumerate(values):
        t = i / (len(values) - 1)
        px = inner.x + t * inner.w
        py = inner.y + inner.h - ((v - mn) / (mx - mn)) * inner.h
        pts.append((px, py))
    if len(pts) >= 2:
        pygame.draw.lines(surface, color, False, pts, 2)


def draw_side_panel(surface, font, small_font, world: World, selected_city: Optional[City], speed: int, paused: bool):
    panel_x = MAP_W
    pygame.draw.rect(surface, (18, 18, 24), (panel_x, 0, PANEL_W, SCREEN_H))
    pygame.draw.rect(surface, (80, 80, 92), (panel_x, 0, PANEL_W, SCREEN_H), 1)

    y = 14
    draw_text(surface, font, 'World Control Room', panel_x + 14, y, (245, 245, 255))
    y += 28
    draw_text(surface, small_font, f'Tick: {world.tick}', panel_x + 14, y); y += 18
    draw_text(surface, small_font, f'Status: {"Paused" if paused else "Running"} x{speed}', panel_x + 14, y); y += 18
    draw_text(surface, small_font, f'Population: {int(world.total_population())}', panel_x + 14, y); y += 18
    draw_text(surface, small_font, f'Wealth: {int(world.total_wealth())}', panel_x + 14, y); y += 18
    draw_text(surface, small_font, f'Average price index: {world.average_price():.1f}', panel_x + 14, y); y += 18
    wars = sum(len(c.at_war) for c in world.countries) // 2
    draw_text(surface, small_font, f'Wars active: {wars}', panel_x + 14, y); y += 18

    y += 8
    if selected_city:
        draw_text(surface, font, selected_city.name, panel_x + 14, y, (240, 240, 240))
        y += 26
        draw_text(surface, small_font, f'Country: {selected_city.country.name}', panel_x + 14, y); y += 18
        draw_text(surface, small_font, f'Specialization: {selected_city.specialization}', panel_x + 14, y); y += 18
        draw_text(surface, small_font, f'Population: {int(selected_city.population)}', panel_x + 14, y); y += 18
        draw_text(surface, small_font, f'Wealth: {int(selected_city.wealth)}', panel_x + 14, y); y += 18
        draw_text(surface, small_font, f'Treasury: {int(selected_city.country.treasury)}', panel_x + 14, y); y += 18
        draw_text(surface, small_font, f'Local biome: {selected_city.tile.biome}', panel_x + 14, y); y += 18
        draw_text(surface, small_font, f'Active effects: {len(selected_city.effects)}', panel_x + 14, y); y += 20

        # stock display
        draw_text(surface, small_font, 'Stockpiles', panel_x + 14, y, (220, 220, 230))
        y += 18
        for g in ('food', 'wood', 'iron', 'copper', 'tools', 'weapons', 'cloth', 'carts', 'luxuries'):
            val = selected_city.stock.get(g, 0.0)
            draw_text(surface, small_font, f'{g:>8}: {int(val)}', panel_x + 14, y)
            y += 16
        y += 6
        draw_text(surface, small_font, 'Prices', panel_x + 14, y, (220, 220, 230))
        y += 18
        for g in ('food', 'iron', 'tools', 'weapons', 'cloth', 'luxuries'):
            draw_text(surface, small_font, f'{g:>8}: {selected_city.market.prices[g]:.1f}', panel_x + 14, y)
            y += 16

        chart1 = pygame.Rect(panel_x + 10, 610, PANEL_W - 20, 120)
        chart2 = pygame.Rect(panel_x + 10, 740, PANEL_W - 20, 120)
        draw_graph(surface, chart1, list(selected_city.population_history), selected_city.country.color, 'Population trend', small_font)
        draw_graph(surface, chart2, list(selected_city.market.history['food']), (220, 190, 90), 'Food price trend', small_font)
    else:
        draw_text(surface, small_font, 'Click a city to inspect its economy.', panel_x + 14, y, (190, 190, 200))

    # log window
    log_rect = pygame.Rect(panel_x + 10, 870 - 110, PANEL_W - 20, 100)
    pygame.draw.rect(surface, (24, 24, 30), log_rect, border_radius=8)
    pygame.draw.rect(surface, (80, 80, 92), log_rect, 1, border_radius=8)
    draw_text(surface, small_font, 'Event log', log_rect.x + 8, log_rect.y + 6, (220, 220, 230))
    ly = log_rect.y + 24
    for line in list(world.log)[:4]:
        draw_text(surface, small_font, line[:48], log_rect.x + 8, ly, (200, 200, 200))
        ly += 18


# ---------------------------- APP ----------------------------

class App:
    def __init__(self):
        pygame.init()
        pygame.display.set_caption('City & Country Economic Simulation - Expanded')
        self.screen = pygame.display.set_mode((SCREEN_W, SCREEN_H))
        self.clock = pygame.time.Clock()
        self.font = pygame.font.SysFont('consolas', 22)
        self.small_font = pygame.font.SysFont('consolas', 16)
        self.world = World()
        self.camera = Camera()
        self.selected_city: Optional[City] = None
        self.paused = False
        self.speed = 2
        self.running = True
        self.step_once = False

    def find_city_at_screen(self, pos):
        mx, my = pos
        if mx >= MAP_W:
            return None
        wx, wy = self.camera.screen_to_world(mx, my)
        for city in sorted(self.world.cities, key=lambda c: c.visual_radius(), reverse=True):
            if dist(wx, wy, city.x, city.y) <= max(8, city.visual_radius() * 2.2):
                return city
        return None

    def regenerate(self):
        self.world = World()
        self.selected_city = None
        self.world.log_event('New world generated')

    def load_world(self):
        if os.path.exists(SAVE_FILE):
            self.world = World.load(SAVE_FILE)
            self.selected_city = None
            self.world.log_event('World loaded from save file')

    def update(self):
        if not self.paused or self.step_once:
            steps = self.speed if not self.step_once else 1
            for _ in range(steps):
                self.world.step()
            self.step_once = False

    def draw(self):
        self.screen.fill((10, 10, 14))
        self.world.draw_world(self.screen, self.camera, self.selected_city)
        draw_side_panel(self.screen, self.font, self.small_font, self.world, self.selected_city, self.speed, self.paused)
        # top-left help strip
        help_text = 'Drag: pan | Wheel: zoom | Click city: inspect | Space: pause | +/-: speed | S save | L load | R regen | N step'
        pygame.draw.rect(self.screen, (0, 0, 0), (10, 10, MAP_W - 20, 28), border_radius=6)
        draw_text(self.screen, self.small_font, help_text, 16, 15, (230, 230, 240))
        pygame.display.flip()

    def handle_event(self, event):
        if event.type == pygame.QUIT:
            self.running = False
        elif event.type == pygame.KEYDOWN:
            if event.key == pygame.K_SPACE:
                self.paused = not self.paused
            elif event.key in (pygame.K_PLUS, pygame.K_EQUALS, pygame.K_KP_PLUS):
                self.speed = clamp(self.speed + 1, 1, 16)
            elif event.key in (pygame.K_MINUS, pygame.K_KP_MINUS):
                self.speed = clamp(self.speed - 1, 1, 16)
            elif event.key == pygame.K_s:
                self.world.save(SAVE_FILE)
            elif event.key == pygame.K_l:
                self.load_world()
            elif event.key == pygame.K_r:
                self.regenerate()
            elif event.key == pygame.K_n:
                self.step_once = True
                self.paused = True
            elif event.key == pygame.K_TAB:
                if self.world.cities:
                    if self.selected_city is None:
                        self.selected_city = self.world.cities[0]
                    else:
                        idx = self.world.cities.index(self.selected_city)
                        self.selected_city = self.world.cities[(idx + 1) % len(self.world.cities)]

        elif event.type == pygame.MOUSEBUTTONDOWN:
            if event.button == 1:
                city = self.find_city_at_screen(event.pos)
                self.selected_city = city
            elif event.button == 2 or event.button == 3:
                self.camera.dragging = True
                self.camera.drag_anchor = event.pos
                self.camera.pan_anchor = (self.camera.x, self.camera.y)
            elif event.button == 4:
                self.camera.zoom_at(*event.pos, 1.1)
            elif event.button == 5:
                self.camera.zoom_at(*event.pos, 0.9)
        elif event.type == pygame.MOUSEBUTTONUP:
            if event.button in (2, 3):
                self.camera.dragging = False
        elif event.type == pygame.MOUSEMOTION and self.camera.dragging:
            dx = (self.camera.drag_anchor[0] - event.pos[0]) / self.camera.zoom
            dy = (self.camera.drag_anchor[1] - event.pos[1]) / self.camera.zoom
            self.camera.x = self.camera.pan_anchor[0] + dx
            self.camera.y = self.camera.pan_anchor[1] + dy
            self.camera.clamp_to_world()

    def run(self):
        while self.running:
            self.clock.tick(FPS)
            for event in pygame.event.get():
                self.handle_event(event)
            self.update()
            self.draw()
        pygame.quit()


if __name__ == '__main__':
    App().run()
