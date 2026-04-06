"""
ConsultaCAR — Consulta de imóveis do Cadastro Ambiental Rural
Busca por coordenadas geográficas ou código CAR com base local GeoPackage.
Atualização automática via WFS (geoserver.car.gov.br).

Autor: Gabriel Furiati
Ano: 2025

Dependências: shapely, numpy (+ sqlite3 built-in, tkinter built-in)
"""

import tkinter as tk
from tkinter import ttk, messagebox
import threading
import re
import json
import ssl
import math
import struct
import sqlite3
import logging
import urllib.request
import tempfile
import webbrowser
import zipfile
import sys
from pathlib import Path
from datetime import datetime

# ── CONFIGURAÇÃO ─────────────────────────────────────────────────────────────
if getattr(sys, "frozen", False):
    _BASE_DIR = Path(sys.executable).parent
else:
    _BASE_DIR = Path(__file__).parent

# Dependências embutidas na pasta lib/
sys.path.insert(0, str(_BASE_DIR / "lib"))

try:
    from tkintermapview import TkinterMapView
    _HAS_MAP = True
except Exception as _map_err:
    _HAS_MAP = False
    print(f"[AVISO] tkintermapview não carregou: {_map_err}")

PASTA_DADOS = _BASE_DIR / "dados"
CAMINHO_CAR = PASTA_DADOS / "car_rj.gpkg"
LAYER_CAR = "car_rj"

WFS_URL = "https://geoserver.car.gov.br/geoserver/sicar/wfs"
WFS_LAYER = "sicar:sicar_imoveis_rj"
WFS_BATCH = 10000
WFS_RETRIES = 3
WFS_TOTAL_ESTIMADO = 67_000  # para barra de progresso

TILE_SATELITE = "https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}"

# ── LOGGING ──────────────────────────────────────────────────────────────────
PASTA_DADOS.mkdir(parents=True, exist_ok=True)
_LOG_PATH = PASTA_DADOS / "consulta_car.log"

logging.basicConfig(
    filename=str(_LOG_PATH),
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
    encoding="utf-8",
)
log = logging.getLogger("consulta_car")
# ─────────────────────────────────────────────────────────────────────────────

# ── CORES CAR ────────────────────────────────────────────────────────────────
BRANCO = "#FFFFFF"
CINZA_BG = "#F5F5F5"
CINZA_CLARO = "#E8E8E8"
CINZA_MEDIO = "#999999"
CINZA_TEXTO = "#333333"
VERDE_ESCURO = "#006634"
VERDE_MEDIO = "#2E8B57"
VERDE_CLARO = "#8BC34A"
VERDE_HOVER = "#005528"
VERDE_SUCESSO = "#2E7D32"
VERMELHO = "#C62828"
BORDA = "#C8C8C8"
# ─────────────────────────────────────────────────────────────────────────────

def _fmt_num(n):
    """Formata número com separador de milhar brasileiro (ponto)."""
    return f"{n:,}".replace(",", ".")

# Estado global
car_geoms = None       # list[shapely.Geometry]
car_attrs = None       # list[dict]
car_tree = None        # shapely.STRtree
car_idx_cod = {}       # dict[str, int] — índice código CAR → posição
car_count = 0
carregando = False
atualizando = False

# Lazy imports shapely
_from_wkb = None
_STRtree = None
_Point = None

# Correções de acentuação
_CORRECOES = {
    "Aguardando analise": "Aguardando análise",
}


def _init_geo():
    """Import shapely uma única vez."""
    global _from_wkb, _STRtree, _Point
    if _from_wkb is None:
        from shapely import from_wkb, STRtree
        from shapely.geometry import Point
        _from_wkb = from_wkb
        _STRtree = STRtree
        _Point = Point
        log.info("Shapely carregado com sucesso")


# ── GPKG helpers ─────────────────────────────────────────────────────────────

def _gpkg_to_wkb(blob):
    """Strip GeoPackage binary header, return standard WKB."""
    if blob is None or len(blob) < 8:
        return None
    flags = blob[3]
    envelope_type = (flags >> 1) & 0x07
    envelope_sizes = {0: 0, 1: 32, 2: 48, 3: 48, 4: 64}
    wkb_offset = 8 + envelope_sizes.get(envelope_type, 0)
    return bytes(blob[wkb_offset:])


def _haversine_m(lat1, lon1, lat2, lon2):
    """Distância em metros entre dois pontos WGS84 (fórmula de Haversine)."""
    R = 6_371_000.0
    dlat = math.radians(lat2 - lat1)
    dlon = math.radians(lon2 - lon1)
    a = (math.sin(dlat / 2) ** 2 +
         math.cos(math.radians(lat1)) * math.cos(math.radians(lat2)) *
         math.sin(dlon / 2) ** 2)
    return R * 2 * math.asin(math.sqrt(a))


def _detect_geom_col(cursor, table):
    """Detecta coluna de geometria via gpkg_geometry_columns ou fallback."""
    try:
        cursor.execute(
            "SELECT column_name FROM gpkg_geometry_columns WHERE table_name = ?",
            (table,),
        )
        row = cursor.fetchone()
        if row:
            return row[0]
    except Exception:
        pass
    cursor.execute(f"PRAGMA table_info({table})")
    cols = [r[1] for r in cursor.fetchall()]
    for candidate in ("geom", "geometry", "GEOMETRY", "the_geom"):
        if candidate in cols:
            return candidate
    return cols[0] if cols else "geom"


def _detect_attr_cols(cursor, table, geom_col):
    """Detecta quais colunas existem na tabela e mapeia para nomes canônicos."""
    cursor.execute(f"PRAGMA table_info({table})")
    existing = {r[1] for r in cursor.fetchall()}
    existing.discard(geom_col)
    existing.discard("fid")
    aliases = {
        "cod_imovel": ["cod_imovel"],
        "municipio": ["municipio", "nom_municipio"],
        "num_area": ["num_area", "area", "area_ha"],
        "ind_status": ["ind_status", "status_imovel", "status"],
        "ind_tipo": ["ind_tipo", "tipo_imovel", "tipo"],
        "des_condic": ["des_condic", "condicao"],
        "m_fiscal": ["m_fiscal"],
        "dat_criacao": ["dat_criacao"],
        "cod_municipio_ibge": ["cod_municipio_ibge"],
        "uf": ["uf"],
    }
    found = []
    for canonical, candidates in aliases.items():
        for c in candidates:
            if c in existing:
                found.append((canonical, c))
                break
    return found


def _load_car_from_gpkg():
    """Carrega dados CAR do GPKG para memória. Retorna quantidade de imóveis."""
    global car_geoms, car_attrs, car_tree, car_count
    _init_geo()

    log.info("Carregando GPKG: %s", CAMINHO_CAR)
    geoms = []
    attrs = []
    erros = 0

    try:
        conn = sqlite3.connect(str(CAMINHO_CAR))
        cur = conn.cursor()

        geom_col = _detect_geom_col(cur, LAYER_CAR)
        attr_mapping = _detect_attr_cols(cur, LAYER_CAR, geom_col)
        log.info("Coluna geometria: %s | Colunas: %s", geom_col, [c for c, _ in attr_mapping])

        sql_cols = ", ".join([geom_col] + [actual for _, actual in attr_mapping])
        canonical_names = [canon for canon, _ in attr_mapping]

        cur.execute(f"SELECT {sql_cols} FROM {LAYER_CAR}")

        for row in cur:
            wkb = _gpkg_to_wkb(row[0])
            if wkb is None:
                erros += 1
                continue
            geoms.append(_from_wkb(wkb))
            attr = {}
            for i, canon in enumerate(canonical_names):
                attr[canon] = row[i + 1]
            attrs.append(attr)
    finally:
        conn.close()

    car_geoms = geoms
    car_attrs = attrs
    car_tree = _STRtree(geoms)
    car_count = len(geoms)

    # Índice de código CAR para busca O(1)
    car_idx_cod.clear()
    for i, a in enumerate(attrs):
        cod = (a.get("cod_imovel") or "").strip().upper()
        if cod:
            car_idx_cod[cod] = i

    log.info("GPKG carregado: %d imóveis (%d erros de geometria)", car_count, erros)
    return car_count


# ── GPKG writer (for WFS download) ──────────────────────────────────────────

def _geom_to_gpkg_blob(shapely_geom, srs_id=4326):
    """Converte geometria shapely para formato binário GeoPackage."""
    wkb = shapely_geom.wkb
    minx, miny, maxx, maxy = shapely_geom.bounds
    header = struct.pack('<2sBBi4d',
                         b'GP', 0, 0x03, srs_id,
                         minx, maxx, miny, maxy)
    return header + wkb


def _create_gpkg(filepath, layer_name, features, srs_id=4326):
    """Cria um GeoPackage válido a partir de features GeoJSON."""
    from shapely.geometry import shape

    log.info("Criando GPKG: %s (%d features)", filepath, len(features))

    conn = sqlite3.connect(str(filepath))
    try:
        conn.execute("PRAGMA journal_mode=WAL")
        c = conn.cursor()

        # Tabelas de metadados obrigatórias do GPKG
        c.execute("""CREATE TABLE gpkg_spatial_ref_sys (
            srs_name TEXT NOT NULL,
            srs_id INTEGER NOT NULL PRIMARY KEY,
            organization TEXT NOT NULL,
            organization_coordsys_id INTEGER NOT NULL,
            definition TEXT NOT NULL,
            description TEXT
        )""")

        c.execute("""INSERT INTO gpkg_spatial_ref_sys VALUES
            ('WGS 84 geodetic', 4326, 'EPSG', 4326,
             'GEOGCS["WGS 84",DATUM["WGS_1984",SPHEROID["WGS 84",6378137,298.257223563]],PRIMEM["Greenwich",0],UNIT["degree",0.0174532925199433]]',
             'WGS 84')""")
        c.execute("""INSERT INTO gpkg_spatial_ref_sys VALUES
            ('Undefined Cartesian SRS', -1, 'NONE', -1, 'undefined', NULL)""")
        c.execute("""INSERT INTO gpkg_spatial_ref_sys VALUES
            ('Undefined geographic SRS', 0, 'NONE', 0, 'undefined', NULL)""")

        c.execute("""CREATE TABLE gpkg_contents (
            table_name TEXT NOT NULL PRIMARY KEY,
            data_type TEXT NOT NULL,
            identifier TEXT,
            description TEXT DEFAULT '',
            last_change DATETIME NOT NULL,
            min_x DOUBLE, min_y DOUBLE, max_x DOUBLE, max_y DOUBLE,
            srs_id INTEGER,
            FOREIGN KEY (srs_id) REFERENCES gpkg_spatial_ref_sys(srs_id)
        )""")

        c.execute("""CREATE TABLE gpkg_geometry_columns (
            table_name TEXT NOT NULL,
            column_name TEXT NOT NULL,
            geometry_type_name TEXT NOT NULL,
            srs_id INTEGER NOT NULL,
            z TINYINT NOT NULL,
            m TINYINT NOT NULL,
            PRIMARY KEY (table_name, column_name),
            FOREIGN KEY (table_name) REFERENCES gpkg_contents(table_name),
            FOREIGN KEY (srs_id) REFERENCES gpkg_spatial_ref_sys(srs_id)
        )""")

        # Tabela de dados
        c.execute(f"""CREATE TABLE {layer_name} (
            fid INTEGER PRIMARY KEY AUTOINCREMENT,
            geom BLOB,
            cod_imovel TEXT,
            municipio TEXT,
            num_area REAL,
            ind_status TEXT,
            ind_tipo TEXT,
            des_condic TEXT
        )""")

        # Inserir features
        min_x = min_y = float("inf")
        max_x = max_y = float("-inf")
        erros = 0

        for feat in features:
            try:
                props = feat.get("properties", {})
                geom = shape(feat["geometry"])
                gpkg_blob = _geom_to_gpkg_blob(geom, srs_id)

                bx0, by0, bx1, by1 = geom.bounds
                min_x = min(min_x, bx0)
                min_y = min(min_y, by0)
                max_x = max(max_x, bx1)
                max_y = max(max_y, by1)

                area_val = props.get("area") or props.get("num_area")
                try:
                    area_val = float(area_val)
                except (TypeError, ValueError):
                    area_val = None

                c.execute(
                    f"INSERT INTO {layer_name} (geom, cod_imovel, municipio, num_area, ind_status, ind_tipo, des_condic) "
                    f"VALUES (?, ?, ?, ?, ?, ?, ?)",
                    (gpkg_blob,
                     props.get("cod_imovel"),
                     props.get("municipio") or props.get("nom_municipio"),
                     area_val,
                     props.get("status_imovel") or props.get("ind_status"),
                     props.get("tipo_imovel") or props.get("ind_tipo"),
                     props.get("condicao") or props.get("des_condic")),
                )
            except Exception as e:
                erros += 1
                log.warning("Erro ao inserir feature: %s", e)

        # Metadados
        c.execute(
            "INSERT INTO gpkg_contents VALUES (?, 'features', ?, '', ?, ?, ?, ?, ?, ?)",
            (layer_name, layer_name, datetime.utcnow().isoformat() + 'Z',
             min_x, min_y, max_x, max_y, srs_id),
        )
        c.execute(
            "INSERT INTO gpkg_geometry_columns VALUES (?, 'geom', 'MULTIPOLYGON', ?, 0, 0)",
            (layer_name, srs_id),
        )

        conn.commit()
    finally:
        conn.close()
    log.info("GPKG criado com sucesso (%d erros)", erros)


# ── Parsing de coordenadas ───────────────────────────────────────────────────

def parse_dms(texto):
    """Converte texto em graus/minutos/segundos para decimal."""
    texto = texto.strip().upper().replace(",", ".")
    m = re.match(
        r"(\d{1,3})[°º\s]+(\d{1,2})['\s]+(\d{1,2}(?:\.\d+)?)[\"″\s]*([NSEW])?",
        texto,
    )
    if not m:
        return None
    grau, minu, seg, direcao = float(m[1]), float(m[2]), float(m[3]), m[4]
    dec = grau + minu / 60 + seg / 3600
    if direcao in ("S", "W"):
        dec = -dec
    return dec


def parse_coordenada(texto):
    """
    Interpreta coordenada em diversos formatos:
      - Graus decimais: -22.053414, -42.362494
      - Graus decimais com ponto-e-vírgula: -22.053414; -42.362494
      - DMS: 22°03'12,29" S 42°21'44,98" W
    Retorna (lat, lon) ou (None, None) se não reconhecido.
    """
    if not texto or not texto.strip():
        return None, None
    texto = texto.strip()

    # Tentar número único
    try:
        val = float(texto.replace(",", "."))
        return val, None
    except ValueError:
        pass

    # Tentar par separado por ; ou espaço
    for sep in [";", "  ", " "]:
        if sep in texto:
            partes = [p.strip() for p in texto.split(sep, 1)]
            if len(partes) == 2:
                try:
                    return float(partes[0].replace(",", ".")), float(partes[1].replace(",", "."))
                except ValueError:
                    pass

    # Tentar par separado por vírgula
    if "," in texto:
        partes = [p.strip() for p in texto.split(",", 1)]
        if len(partes) == 2:
            try:
                return float(partes[0].replace(",", ".")), float(partes[1].replace(",", "."))
            except ValueError:
                pass

    # Tentar DMS
    dms_partes = re.findall(
        r"\d{1,3}[°º\s]+\d{1,2}['\s]+\d{1,2}(?:[.,]\d+)?[\"″\s]*[NSEW]?",
        texto.upper().replace(",", "."),
    )
    if len(dms_partes) >= 2:
        return parse_dms(dms_partes[0]), parse_dms(dms_partes[1])
    if len(dms_partes) == 1:
        return parse_dms(dms_partes[0]), None

    return None, None


# ── Data loading ─────────────────────────────────────────────────────────────

def carregar_car_thread(callback_status, callback_pronto, root):
    """Carrega a base CAR em background thread."""
    global carregando
    carregando = True

    def update(msg, cor=CINZA_MEDIO):
        root.after(0, lambda: callback_status(msg, cor))

    if not CAMINHO_CAR.exists():
        log.warning("Base não encontrada: %s", CAMINHO_CAR)
        update("Base não encontrada — clique em 'Atualizar Base'", VERMELHO)
        carregando = False
        return

    update("Carregando base CAR...", CINZA_MEDIO)

    try:
        count = _load_car_from_gpkg()

        info_path = PASTA_DADOS / "atualizacao.txt"
        data_info = ""
        if info_path.exists():
            data_info = f" (atualizado em {info_path.read_text().strip()})"

        update(
            f"Base carregada: {_fmt_num(count)} imóveis{data_info}",
            VERDE_SUCESSO,
        )
        root.after(0, callback_pronto)
    except Exception as e:
        log.exception("Erro ao carregar base CAR")
        update(f"Erro ao carregar: {e}", VERMELHO)

    carregando = False


# ── Consulta espacial ────────────────────────────────────────────────────────

def consultar(lat, lon):
    """Consulta o CAR para uma coordenada. Retorna lista de dicts (pode ter múltiplos)."""
    pt = _Point(lon, lat)
    log.info("Consulta: lat=%.6f, lon=%.6f", lat, lon)
    resultados = []

    # 1) Busca exata via STRtree — pode haver múltiplos imóveis
    hits = car_tree.query(pt, predicate="intersects")
    if len(hits) > 0:
        for idx in hits:
            idx = int(idx)
            cod = car_attrs[idx].get("cod_imovel", "?")
            log.info("Encontrado (dentro): %s", cod)
            r = _extrair(car_attrs[idx], 0, "Dentro do imóvel")
            r["_geom_idx"] = idx
            resultados.append(r)
        return resultados

    # 2) Vizinho mais próximo
    idx = car_tree.nearest(pt)
    if idx is None:
        log.info("Nenhum CAR encontrado")
        return []
    idx = int(idx)

    # 3) Distância métrica via nearest_points + haversine
    from shapely.ops import nearest_points
    _, nearest_pt = nearest_points(pt, car_geoms[idx])
    dist_m = _haversine_m(lat, lon, nearest_pt.y, nearest_pt.x)

    if dist_m <= 500:
        cod = car_attrs[idx].get("cod_imovel", "?")
        log.info("Encontrado (próximo %.0fm): %s", dist_m, cod)
        r = _extrair(car_attrs[idx], dist_m, f"Próximo ({dist_m:.0f}m)")
        r["_geom_idx"] = idx
        return [r]

    log.info("CAR mais próximo a %.0fm (acima do limite de 500m)", dist_m)
    return []


def consultar_por_codigo(codigo):
    """Busca imóvel CAR pelo código. Retorna dict ou None."""
    codigo = codigo.strip().upper()
    idx = car_idx_cod.get(codigo)
    if idx is not None:
        r = _extrair(car_attrs[idx], 0, "Busca por código")
        r["_geom_idx"] = idx
        return r
    return None


def consulta_lote(coordenadas):
    """Processa lista de (lat, lon) e retorna lista de resultados.
    Cada item: {'lat': ..., 'lon': ..., 'resultados': [...]}.
    """
    resultados = []
    for lat, lon in coordenadas:
        try:
            res = consultar(lat, lon)
            resultados.append({"lat": lat, "lon": lon, "resultados": res})
        except Exception as e:
            log.warning("Erro em lote lat=%.6f lon=%.6f: %s", lat, lon, e)
            resultados.append({"lat": lat, "lon": lon, "resultados": [], "erro": str(e)})
    return resultados


def _extrair(attrs, dist, obs):
    """Extrai campos do imóvel — compatível com formato antigo e WFS."""
    def g(*nomes):
        for n in nomes:
            v = attrs.get(n)
            if v is not None and str(v).strip():
                val = str(v).strip()
                for errado, certo in _CORRECOES.items():
                    if errado in val:
                        val = val.replace(errado, certo)
                return val
        return ""

    return {
        "cod_imovel": g("cod_imovel"),
        "municipio": g("municipio", "nom_municipio"),
        "area_ha": g("num_area", "area", "area_ha"),
        "tipo": g("ind_tipo", "tipo_imovel", "tipo"),
        "status": g("ind_status", "status_imovel", "status"),
        "condicao": g("des_condic", "condicao"),
        "modulos_fiscais": g("m_fiscal"),
        "data_criacao": g("dat_criacao"),
        "distancia": f"{dist:.0f}m" if dist > 0 else "",
        "observacao": obs,
    }


# ── Histórico de consultas ───────────────────────────────────────────────────

_HISTORICO_DB = PASTA_DADOS / "historico.db"


def _init_historico():
    """Cria tabela de histórico se não existir."""
    conn = sqlite3.connect(str(_HISTORICO_DB))
    try:
        conn.execute("""CREATE TABLE IF NOT EXISTS historico (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            data TEXT NOT NULL,
            lat REAL NOT NULL,
            lon REAL NOT NULL,
            cod_imovel TEXT,
            municipio TEXT,
            area_ha TEXT,
            status TEXT,
            observacao TEXT
        )""")
        conn.commit()
    finally:
        conn.close()


def salvar_historico(lat, lon, resultado):
    """Salva uma consulta no histórico. Mantém no máximo 500 registros."""
    _init_historico()
    conn = sqlite3.connect(str(_HISTORICO_DB))
    try:
        conn.execute(
            "INSERT INTO historico (data, lat, lon, cod_imovel, municipio, area_ha, status, observacao) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
            (
                datetime.now().strftime("%d/%m/%Y %H:%M"),
                lat, lon,
                resultado.get("cod_imovel", ""),
                resultado.get("municipio", ""),
                resultado.get("area_ha", ""),
                resultado.get("status", ""),
                resultado.get("observacao", ""),
            ),
        )
        # Manter apenas os 500 registros mais recentes
        conn.execute(
            "DELETE FROM historico WHERE id NOT IN "
            "(SELECT id FROM historico ORDER BY id DESC LIMIT 500)"
        )
        conn.commit()
    finally:
        conn.close()


def carregar_historico(limite=50):
    """Carrega últimas consultas do histórico."""
    _init_historico()
    conn = sqlite3.connect(str(_HISTORICO_DB))
    try:
        cur = conn.execute(
            "SELECT id, data, lat, lon, cod_imovel, municipio, area_ha, status, observacao "
            "FROM historico ORDER BY id DESC LIMIT ?",
            (limite,),
        )
        cols = ["id", "data", "lat", "lon", "cod_imovel", "municipio", "area_ha", "status", "observacao"]
        return [dict(zip(cols, row)) for row in cur.fetchall()]
    finally:
        conn.close()


def limpar_historico():
    """Remove todo o histórico."""
    _init_historico()
    conn = sqlite3.connect(str(_HISTORICO_DB))
    try:
        conn.execute("DELETE FROM historico")
        conn.commit()
    finally:
        conn.close()


# ── WFS download ─────────────────────────────────────────────────────────────

def _wfs_fetch_batch(url, ctx):
    """Baixa um lote do WFS com retry automático."""
    import time
    import urllib.error
    import socket
    for tentativa in range(1, WFS_RETRIES + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "ConsultaCAR/1.0"})
            with urllib.request.urlopen(req, context=ctx, timeout=120) as resp:
                return json.loads(resp.read().decode("utf-8"))
        except (urllib.error.URLError, socket.timeout, ConnectionError, OSError) as e:
            log.warning("WFS tentativa %d/%d falhou (rede): %s", tentativa, WFS_RETRIES, e)
            if tentativa == WFS_RETRIES:
                raise
            time.sleep(3 * tentativa)


def baixar_wfs(progress_callback=None, cancel_check=None):
    """Baixa todos os imóveis CAR-RJ via WFS em lotes paralelos com retry."""
    from concurrent.futures import ThreadPoolExecutor, as_completed

    log.info("Iniciando download WFS paralelo: %s", WFS_LAYER)

    # SSL flexível: servidor do CAR usa ciphers antigos e certificados
    # problemáticos — necessário desabilitar verificação (limitação gov.br)
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    ctx.check_hostname = False
    ctx.verify_mode = ssl.CERT_NONE
    ctx.set_ciphers("DEFAULT:@SECLEVEL=1")

    # Gerar offsets para download paralelo (7 threads x 10k = 70k features)
    offsets = list(range(0, WFS_TOTAL_ESTIMADO + WFS_BATCH, WFS_BATCH))
    all_features = [None] * len(offsets)  # manter ordem
    total_baixado = [0]  # running total thread-safe via lista

    def fetch_slot(slot_idx, offset):
        """Baixa um lote e armazena na posição correta."""
        url = (
            f"{WFS_URL}?service=WFS&version=2.0.0&request=GetFeature"
            f"&typeName={WFS_LAYER}"
            f"&outputFormat=application/json"
            f"&count={WFS_BATCH}&startIndex={offset}"
        )
        data = _wfs_fetch_batch(url, ctx)
        features = data.get("features", [])
        all_features[slot_idx] = features
        total_baixado[0] += len(features)
        log.info("WFS lote %d (offset=%d): %d features", slot_idx, offset, len(features))
        return len(features)

    WFS_WORKERS = 4  # threads paralelas

    with ThreadPoolExecutor(max_workers=WFS_WORKERS) as pool:
        futures = {}
        for i, off in enumerate(offsets):
            if cancel_check and cancel_check():
                log.info("Download WFS cancelado pelo usuário")
                return None
            futures[pool.submit(fetch_slot, i, off)] = i

        for future in as_completed(futures):
            if cancel_check and cancel_check():
                log.info("Download WFS cancelado pelo usuário")
                return None
            try:
                future.result()
            except Exception as e:
                log.error("Erro no lote %d: %s", futures[future], e)
                raise

            pct = min(95, int(total_baixado[0] / WFS_TOTAL_ESTIMADO * 100))
            if progress_callback:
                progress_callback(
                    f"Baixando... {_fmt_num(total_baixado[0])} imóveis ({pct}%)"
                )

    # Juntar tudo em ordem
    merged = []
    for slot in all_features:
        if slot:
            merged.extend(slot)
    all_features = merged

    if not all_features:
        raise Exception("Nenhum dado retornado do WFS")

    if progress_callback:
        progress_callback(f"Salvando {_fmt_num(len(all_features))} imóveis...")

    PASTA_DADOS.mkdir(parents=True, exist_ok=True)

    import shutil
    if CAMINHO_CAR.exists():
        backup = PASTA_DADOS / f"car_rj_backup_{datetime.now().strftime('%Y%m%d_%H%M')}.gpkg"
        shutil.copy2(str(CAMINHO_CAR), str(backup))
        log.info("Backup criado: %s", backup.name)

    tmp_gpkg = PASTA_DADOS / "car_rj_tmp.gpkg"
    _create_gpkg(tmp_gpkg, LAYER_CAR, all_features)
    if CAMINHO_CAR.exists():
        CAMINHO_CAR.unlink()
    tmp_gpkg.rename(CAMINHO_CAR)

    info_path = PASTA_DADOS / "atualizacao.txt"
    info_path.write_text(datetime.now().strftime("%d/%m/%Y %H:%M"))

    log.info("Download WFS concluído: %d imóveis", len(all_features))
    return len(all_features)


# ── GUI ──────────────────────────────────────────────────────────────────────

class App:

    def __init__(self, root):
        self.root = root
        self.cancel_update = False
        self._last_resultado = None
        self._last_resultados = []  # múltiplos resultados
        self._resultado_idx = 0     # índice do resultado atual
        self._last_lat = 0
        self._last_lon = 0
        root.title("ConsultaCAR")
        root.configure(bg=BRANCO)
        root.resizable(True, True)

        w, h = 1200, 720
        x = (root.winfo_screenwidth() - w) // 2
        y = (root.winfo_screenheight() - h) // 2
        root.geometry(f"{w}x{h}+{x}+{y}")
        root.minsize(900, 600)

        # ── Estilos ──
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("TFrame", background=BRANCO)
        style.configure("Card.TFrame", background=CINZA_BG)
        style.configure("TLabel", background=BRANCO, foreground=CINZA_TEXTO, font=("Segoe UI", 10))
        style.configure("Title.TLabel", background=BRANCO, foreground=VERDE_ESCURO, font=("Segoe UI", 20, "bold"))
        style.configure("Subtitle.TLabel", background=BRANCO, foreground=CINZA_MEDIO, font=("Segoe UI", 9))
        style.configure("Status.TLabel", background=BRANCO, foreground=CINZA_MEDIO, font=("Segoe UI", 9))
        style.configure("FieldLabel.TLabel", background=CINZA_BG, foreground=CINZA_MEDIO, font=("Segoe UI", 9))
        style.configure("FieldValue.TLabel", background=CINZA_BG, foreground=CINZA_TEXTO, font=("Segoe UI", 11, "bold"))
        style.configure("CAR.TLabel", background=CINZA_BG, foreground=VERDE_ESCURO, font=("Consolas", 11, "bold"))
        style.configure("Obs.TLabel", background=CINZA_BG, foreground=VERDE_SUCESSO, font=("Segoe UI", 9, "bold"))
        style.configure("DataAtual.TLabel", background=BRANCO, foreground=CINZA_MEDIO, font=("Segoe UI", 8))
        style.configure("Nav.TLabel", background=CINZA_BG, foreground=VERDE_ESCURO, font=("Segoe UI", 9, "bold"))

        style.configure("Green.TButton",
                        background=VERDE_ESCURO, foreground=BRANCO,
                        font=("Segoe UI", 11, "bold"), padding=(20, 10), borderwidth=0)
        style.map("Green.TButton",
                  background=[("active", VERDE_HOVER), ("disabled", CINZA_CLARO)],
                  foreground=[("disabled", CINZA_MEDIO)])

        style.configure("Update.TButton",
                        background=VERDE_MEDIO, foreground=BRANCO,
                        font=("Segoe UI", 9, "bold"), padding=(10, 5), borderwidth=0)
        style.map("Update.TButton",
                  background=[("active", VERDE_ESCURO), ("disabled", CINZA_CLARO)])

        # ── Barra verde topo ──
        tk.Frame(root, bg=VERDE_ESCURO, height=4).pack(fill="x")

        # ── Container principal (esquerda: controles / direita: mapa) ──
        main_container = ttk.Frame(root, style="TFrame")
        main_container.pack(fill="both", expand=True)

        self.left_panel = ttk.Frame(main_container, style="TFrame", width=640)
        self.left_panel.pack(side="left", fill="y")
        self.left_panel.pack_propagate(False)

        # ── Mapa embutido (painel direito) ──
        map_frame = tk.Frame(main_container, bg=CINZA_CLARO,
                             highlightthickness=1, highlightbackground=BORDA)
        map_frame.pack(side="right", fill="both", expand=True, padx=(0, 10), pady=10)

        if _HAS_MAP:
            self.map_widget = TkinterMapView(map_frame, corner_radius=0)
            self.map_widget.pack(fill="both", expand=True)
            self.map_widget.set_tile_server(TILE_SATELITE)
            self.map_widget.set_position(-22.3, -43.2)
            self.map_widget.set_zoom(8)
        else:
            self.map_widget = None
            ttk.Label(map_frame,
                      text="Mapa indisponível",
                      font=("Segoe UI", 10), foreground=CINZA_MEDIO,
                      background=CINZA_CLARO).pack(expand=True)

        # ── Header ──
        header = ttk.Frame(self.left_panel, style="TFrame")
        header.pack(fill="x", padx=30, pady=(20, 5))

        title_row = ttk.Frame(header, style="TFrame")
        title_row.pack(fill="x")

        ttk.Label(title_row, text="CONSULTA CAR", style="Title.TLabel").pack(side="left", anchor="w")

        update_col = ttk.Frame(title_row, style="TFrame")
        update_col.pack(side="right", anchor="e")

        self.lbl_data_atualizacao = ttk.Label(
            update_col, text=self._get_data_atualizacao(), style="DataAtual.TLabel"
        )
        self.lbl_data_atualizacao.pack(anchor="e")

        self.btn_atualizar = ttk.Button(
            update_col, text="⟳ Atualizar Base",
            style="Update.TButton", command=self.on_atualizar
        )
        self.btn_atualizar.pack(anchor="e", pady=(3, 0))

        ttk.Label(header, text="Coordenada, código CAR ou importar CSV",
                  style="Subtitle.TLabel").pack(anchor="w", pady=(2, 0))

        # ── Separador ──
        tk.Frame(self.left_panel, bg=VERDE_CLARO, height=2).pack(fill="x", padx=30, pady=(12, 15))

        # ── Input ──
        input_frame = ttk.Frame(self.left_panel, style="TFrame")
        input_frame.pack(fill="x", padx=30)

        ttk.Label(input_frame, text="BUSCA",
                  font=("Segoe UI", 9, "bold"),
                  foreground=VERDE_ESCURO, background=BRANCO).pack(anchor="w")
        ttk.Label(input_frame,
                  text='Coordenada ou código CAR (ex: RJ-3304557-...)',
                  style="Subtitle.TLabel").pack(anchor="w", pady=(0, 5))

        self.entry = tk.Entry(input_frame,
                              font=("Consolas", 14),
                              bg=BRANCO, fg=CINZA_TEXTO,
                              insertbackground=VERDE_ESCURO,
                              selectbackground=VERDE_CLARO,
                              selectforeground=CINZA_TEXTO,
                              relief="flat", bd=0,
                              highlightthickness=2,
                              highlightcolor=VERDE_ESCURO,
                              highlightbackground=BORDA)
        self.entry.pack(fill="x", ipady=10, pady=(0, 10))
        self.entry.bind("<Return>", lambda e: self.on_consultar())
        self.entry.focus_set()

        # ── Botões principais ──
        btn_row = ttk.Frame(input_frame, style="TFrame")
        btn_row.pack(fill="x", pady=(0, 5))

        self.btn = ttk.Button(btn_row, text="CONSULTAR",
                              style="Green.TButton", command=self.on_consultar,
                              state="disabled")
        self.btn.pack(side="left", padx=(0, 8))

        tk.Button(btn_row, text="IMPORTAR CSV",
                  font=("Segoe UI", 9, "bold"),
                  bg="#1565C0", fg=BRANCO,
                  activebackground="#0D47A1", activeforeground=BRANCO,
                  relief="flat", bd=0, padx=12, pady=8, cursor="hand2",
                  command=self._importar_csv).pack(side="left", padx=(0, 8))

        tk.Button(btn_row, text="HISTÓRICO",
                  font=("Segoe UI", 9, "bold"),
                  bg=CINZA_MEDIO, fg=BRANCO,
                  activebackground=CINZA_TEXTO, activeforeground=BRANCO,
                  relief="flat", bd=0, padx=12, pady=8, cursor="hand2",
                  command=self._mostrar_historico).pack(side="left", padx=(0, 8))

        tk.Button(btn_row, text="LIMPAR",
                  font=("Segoe UI", 8),
                  bg=CINZA_CLARO, fg=CINZA_MEDIO,
                  activebackground=CINZA_MEDIO, activeforeground=BRANCO,
                  relief="flat", bd=0, padx=10, pady=8, cursor="hand2",
                  command=self._limpar).pack(side="left")

        # ── Status ──
        self.status_label = ttk.Label(self.left_panel, text="Inicializando...", style="Status.TLabel")
        self.status_label.pack(padx=30, anchor="w")

        # ── Barra de progresso (oculta inicialmente) ──
        style.configure("green.Horizontal.TProgressbar",
                        troughcolor=CINZA_CLARO, background=VERDE_MEDIO)
        self.progress_frame = ttk.Frame(self.left_panel, style="TFrame")
        self.progress = ttk.Progressbar(self.progress_frame, mode="determinate", length=580, maximum=100,
                                        style="green.Horizontal.TProgressbar")
        self.progress.pack(fill="x")

        # ── Resultado (scrollable) ──
        self.result_frame = tk.Frame(self.left_panel, bg=CINZA_BG, highlightthickness=1,
                                     highlightbackground=BORDA)
        self.result_frame.pack(fill="both", expand=True, padx=30, pady=(15, 25))

        self.result_canvas = tk.Canvas(self.result_frame, bg=CINZA_BG, highlightthickness=0)
        self.result_scrollbar = ttk.Scrollbar(self.result_frame, orient="vertical", command=self.result_canvas.yview)
        self.result_inner = ttk.Frame(self.result_canvas, style="Card.TFrame")

        self._result_win_id = self.result_canvas.create_window((0, 0), window=self.result_inner, anchor="nw")
        self.result_canvas.configure(yscrollcommand=self.result_scrollbar.set)

        # Ajustar largura do inner ao canvas e scrollbar dinâmica
        def _on_result_configure(event=None):
            self.result_canvas.configure(scrollregion=self.result_canvas.bbox("all"))
            # Mostrar/ocultar scrollbar conforme necessidade
            bbox = self.result_canvas.bbox("all")
            if bbox and bbox[3] > self.result_canvas.winfo_height():
                self.result_scrollbar.pack(side="right", fill="y")
            else:
                self.result_scrollbar.pack_forget()

        def _on_canvas_resize(event):
            self.result_canvas.itemconfig(self._result_win_id, width=event.width)

        self.result_inner.bind("<Configure>", _on_result_configure)
        self.result_canvas.bind("<Configure>", _on_canvas_resize)

        self.result_canvas.pack(side="left", fill="both", expand=True, padx=20, pady=15)

        # Scroll com mouse wheel
        def _on_mousewheel(event):
            self.result_canvas.yview_scroll(-1 * (event.delta // 120), "units")
        self.result_canvas.bind("<Enter>", lambda e: self.result_canvas.bind_all("<MouseWheel>", _on_mousewheel))
        self.result_canvas.bind("<Leave>", lambda e: self.result_canvas.unbind_all("<MouseWheel>"))

        self._build_resultado_vazio()

        # ── Rodapé ──
        ttk.Label(self.left_panel, text="ConsultaCAR — github.com/Furiatii/ConsultaCAR",
                  font=("Segoe UI", 8), foreground=CINZA_MEDIO, background=BRANCO).pack(pady=(0, 8))

        # ── Carregar CAR em background ──
        threading.Thread(
            target=carregar_car_thread,
            args=(self._set_status, self._on_base_pronta, root),
            daemon=True,
        ).start()

        log.info("Aplicação iniciada")

    # ── Utilidades ──────────────────────────────────────────────────────────

    def _get_data_atualizacao(self):
        info_path = PASTA_DADOS / "atualizacao.txt"
        if info_path.exists():
            return f"Atualizado em {info_path.read_text().strip()}"
        return "Base local (sem data WFS)"

    def _set_status(self, msg, cor=CINZA_MEDIO):
        self.status_label.config(text=msg, foreground=cor)

    def _on_base_pronta(self):
        self.btn.config(state="normal")

    def _clear_result(self):
        """Remove todos os widgets do painel de resultado."""
        for w in self.result_inner.winfo_children():
            w.destroy()

    def _fmt_area(self, valor):
        """Formata valor de área em hectares no padrão brasileiro."""
        if not valor:
            return ""
        try:
            return f"{float(valor):,.2f} ha".replace(",", "X").replace(".", ",").replace("X", ".")
        except (ValueError, TypeError):
            return str(valor)

    def _fmt_decimal_br(self, valor):
        """Formata número decimal com separadores brasileiros (ponto/vírgula)."""
        if not valor:
            return ""
        try:
            return f"{float(valor):,.2f}".replace(",", "X").replace(".", ",").replace("X", ".")
        except (ValueError, TypeError):
            return str(valor)

    # ── Resultado vazio ─────────────────────────────────────────────────────

    def _build_resultado_vazio(self):
        """Exibe mensagem de aguardando consulta no painel de resultado."""
        self._clear_result()
        ttk.Label(self.result_inner, text="Aguardando consulta...",
                  font=("Segoe UI", 11), foreground=CINZA_MEDIO, background=CINZA_BG).pack(expand=True)

    # ── Exibir resultado único ──────────────────────────────────────────────

    def _mostrar_resultado(self, dados):
        """Renderiza os campos e botões de ação de um resultado individual."""
        campos = [
            ("COD. IMÓVEL", "cod_imovel", "CAR.TLabel"),
            ("MUNICÍPIO", "municipio", "FieldValue.TLabel"),
            ("ÁREA", "area_ha", "FieldValue.TLabel"),
            ("TIPO", "tipo", "FieldValue.TLabel"),
            ("STATUS", "status", "FieldValue.TLabel"),
            ("CONDIÇÃO", "condicao", "FieldValue.TLabel"),
            ("MÓD. FISCAIS", "modulos_fiscais", "FieldValue.TLabel"),
        ]

        for i, (label, key, estilo) in enumerate(campos):
            valor = dados.get(key, "")
            if key == "area_ha":
                valor = self._fmt_area(valor)
            if key == "modulos_fiscais":
                valor = self._fmt_decimal_br(valor)

            row = ttk.Frame(self.result_inner, style="Card.TFrame")
            row.pack(fill="x", pady=(8 if i == 0 else 3, 0))
            ttk.Label(row, text=label, style="FieldLabel.TLabel", width=14, anchor="e").pack(side="left", padx=(0, 10))
            ttk.Label(row, text=valor or "—", style=estilo).pack(side="left", fill="x", expand=True)

        obs = dados.get("observacao", "")
        dist = dados.get("distancia", "")
        obs_text = obs + (f"  ({dist})" if dist else "")

        obs_frame = ttk.Frame(self.result_inner, style="Card.TFrame")
        obs_frame.pack(fill="x", pady=(12, 5))
        ttk.Label(obs_frame, text=obs_text, style="Obs.TLabel").pack(anchor="center")

        # ── Botões de ação ──
        action_frame = ttk.Frame(self.result_inner, style="Card.TFrame")
        action_frame.pack(fill="x", pady=(10, 0))

        tk.Button(action_frame, text="COPIAR CÓDIGO",
                  font=("Segoe UI", 9, "bold"), bg=VERDE_MEDIO, fg=BRANCO,
                  activebackground=VERDE_ESCURO, activeforeground=BRANCO,
                  relief="flat", bd=0, padx=12, pady=5, cursor="hand2",
                  command=lambda: self._copiar(dados.get("cod_imovel", ""))).pack(side="left", padx=(0, 5))

        tk.Button(action_frame, text="COPIAR TUDO",
                  font=("Segoe UI", 9, "bold"), bg=VERDE_MEDIO, fg=BRANCO,
                  activebackground=VERDE_ESCURO, activeforeground=BRANCO,
                  relief="flat", bd=0, padx=12, pady=5, cursor="hand2",
                  command=lambda: self._copiar_completo(dados)).pack(side="left", padx=(0, 5))

        tk.Button(action_frame, text="NAVEGADOR",
                  font=("Segoe UI", 9, "bold"), bg="#1565C0", fg=BRANCO,
                  activebackground="#0D47A1", activeforeground=BRANCO,
                  relief="flat", bd=0, padx=12, pady=5, cursor="hand2",
                  command=lambda: self._ver_mapa(dados)).pack(side="left", padx=(0, 5))

        tk.Button(action_frame, text="KMZ",
                  font=("Segoe UI", 8, "bold"), bg="#E65100", fg=BRANCO,
                  activebackground="#BF360C", activeforeground=BRANCO,
                  relief="flat", bd=0, padx=10, pady=5, cursor="hand2",
                  command=lambda: self._exportar("kmz", dados)).pack(side="left", padx=(0, 5))

        tk.Button(action_frame, text="SHP",
                  font=("Segoe UI", 8, "bold"), bg="#E65100", fg=BRANCO,
                  activebackground="#BF360C", activeforeground=BRANCO,
                  relief="flat", bd=0, padx=10, pady=5, cursor="hand2",
                  command=lambda: self._exportar("shp", dados)).pack(side="left")

    # ── Exibir múltiplos resultados ─────────────────────────────────────────

    def _exibir_resultados(self, resultados):
        """Exibe lista de resultados com navegação e salva no histórico."""
        self._last_resultados = resultados
        self._clear_result()

        if not resultados:
            self._mostrar_nao_encontrado()
            self.status_label.config(text="Nenhum CAR encontrado no raio de 500m", foreground=VERMELHO)
            self._limpar_mapa()
            return

        if len(resultados) > 1:
            nav_frame = ttk.Frame(self.result_inner, style="Card.TFrame")
            nav_frame.pack(fill="x", pady=(0, 5))

            self._nav_label = ttk.Label(nav_frame,
                text=f"Resultado 1 de {len(resultados)}", style="Nav.TLabel")
            self._nav_label.pack(side="left")

            tk.Button(nav_frame, text="◀ Anterior",
                      font=("Segoe UI", 8), bg=CINZA_CLARO, fg=CINZA_TEXTO,
                      relief="flat", bd=0, padx=8, pady=2, cursor="hand2",
                      command=lambda: self._navegar_resultado(-1)).pack(side="right", padx=(5, 0))
            tk.Button(nav_frame, text="Próximo ▶",
                      font=("Segoe UI", 8), bg=CINZA_CLARO, fg=CINZA_TEXTO,
                      relief="flat", bd=0, padx=8, pady=2, cursor="hand2",
                      command=lambda: self._navegar_resultado(1)).pack(side="right")

            tk.Frame(self.result_inner, bg=BORDA, height=1).pack(fill="x", pady=(5, 0))

        self._resultado_idx = 0
        dados = resultados[0]
        self._last_resultado = dados
        self._mostrar_resultado(dados)

        for r in resultados:
            salvar_historico(self._last_lat, self._last_lon, r)

        cod_list = ", ".join(r.get("cod_imovel", "?") for r in resultados)
        n = len(resultados)
        self.status_label.config(
            text=f"{'Encontrados' if n > 1 else 'Encontrado'}: {cod_list}",
            foreground=VERDE_SUCESSO)

        if "_geom_idx" in dados:
            self._atualizar_mapa_multi(resultados, self._last_lat, self._last_lon)

    def _navegar_resultado(self, direcao):
        """Navega entre resultados múltiplos (anterior/próximo)."""
        if not self._last_resultados:
            return
        n = len(self._last_resultados)
        self._resultado_idx = (self._resultado_idx + direcao) % n
        dados = self._last_resultados[self._resultado_idx]
        self._last_resultado = dados

        children = self.result_inner.winfo_children()
        for w in children[2:]:
            w.destroy()

        self._nav_label.config(text=f"Resultado {self._resultado_idx + 1} de {n}")
        self._mostrar_resultado(dados)

        if "_geom_idx" in dados:
            geom = car_geoms[dados["_geom_idx"]]
            self._atualizar_mapa(geom, self._last_lat, self._last_lon)

    def _mostrar_nao_encontrado(self):
        """Exibe mensagem de nenhum CAR encontrado no painel."""
        self._clear_result()
        ttk.Label(self.result_inner, text="NENHUM CAR ENCONTRADO",
                  font=("Segoe UI", 13, "bold"),
                  foreground=VERMELHO, background=CINZA_BG).pack(expand=True, pady=(30, 5))
        ttk.Label(self.result_inner, text="Nenhum imóvel CAR num raio de 500m desta coordenada",
                  foreground=CINZA_MEDIO, background=CINZA_BG, font=("Segoe UI", 10)).pack()

    def _mostrar_erro(self, msg):
        """Exibe mensagem de erro no painel de resultado."""
        self._clear_result()
        ttk.Label(self.result_inner, text=msg, font=("Segoe UI", 11),
                  foreground=VERMELHO, background=CINZA_BG, wraplength=500).pack(expand=True)

    # ── Limpar ──────────────────────────────────────────────────────────────

    def _limpar(self):
        """Limpa campo de entrada, resultado e mapa."""
        self.entry.delete(0, tk.END)
        self._last_resultado = None
        self._last_resultados = []
        self._build_resultado_vazio()
        self._limpar_mapa()
        if car_geoms is not None:
            self.status_label.config(
                text=f"Base carregada: {_fmt_num(car_count)} imóveis",
                foreground=VERDE_SUCESSO)
        self.entry.focus_set()

    # ── Mapa ────────────────────────────────────────────────────────────────

    def _atualizar_mapa(self, geom, lat, lon):
        """Desenha polígono e marcador de um resultado no mapa embutido."""
        if not self.map_widget:
            return
        self.map_widget.delete_all_marker()
        self.map_widget.delete_all_polygon()

        from shapely.geometry import MultiPolygon, Polygon
        if isinstance(geom, MultiPolygon):
            parts = list(geom.geoms)
        elif isinstance(geom, Polygon):
            parts = [geom]
        else:
            return

        for poly in parts:
            coords = [(y, x) for x, y in poly.exterior.coords]
            self.map_widget.set_polygon(coords, fill_color=None,
                                        outline_color="#FFD700", border_width=3)

        self.map_widget.set_marker(lat, lon, text="Ponto consultado",
                                   text_color="#FFFFFF",
                                   marker_color_circle="#1A73E8",
                                   marker_color_outside="#1557B0")

        bounds = geom.bounds
        self.map_widget.fit_bounding_box(
            (bounds[3] + 0.005, bounds[0] - 0.005),
            (bounds[1] - 0.005, bounds[2] + 0.005))

    def _atualizar_mapa_multi(self, resultados, lat, lon):
        """Desenha polígonos de múltiplos resultados com cores distintas no mapa."""
        if not self.map_widget:
            return
        self.map_widget.delete_all_marker()
        self.map_widget.delete_all_polygon()

        from shapely.geometry import MultiPolygon, Polygon
        cores = ["#FFD700", "#FF6B6B", "#4FC3F7", "#81C784", "#FFB74D"]
        all_bounds = []

        for ri, r in enumerate(resultados):
            if "_geom_idx" not in r:
                continue
            geom = car_geoms[r["_geom_idx"]]
            cor = cores[ri % len(cores)]

            if isinstance(geom, MultiPolygon):
                parts = list(geom.geoms)
            elif isinstance(geom, Polygon):
                parts = [geom]
            else:
                continue

            for poly in parts:
                coords = [(y, x) for x, y in poly.exterior.coords]
                self.map_widget.set_polygon(coords, fill_color=None,
                                            outline_color=cor, border_width=3)
            all_bounds.append(geom.bounds)

        self.map_widget.set_marker(lat, lon, text="Ponto consultado",
                                   text_color="#FFFFFF",
                                   marker_color_circle="#1A73E8",
                                   marker_color_outside="#1557B0")

        if all_bounds:
            min_x = min(b[0] for b in all_bounds)
            min_y = min(b[1] for b in all_bounds)
            max_x = max(b[2] for b in all_bounds)
            max_y = max(b[3] for b in all_bounds)
            self.map_widget.fit_bounding_box(
                (max_y + 0.005, min_x - 0.005),
                (min_y - 0.005, max_x + 0.005))

    def _limpar_mapa(self):
        """Remove marcadores e polígonos e reseta o zoom do mapa."""
        if not self.map_widget:
            return
        self.map_widget.delete_all_marker()
        self.map_widget.delete_all_polygon()
        self.map_widget.set_position(-22.3, -43.2)
        self.map_widget.set_zoom(8)

    # ── Copiar ──────────────────────────────────────────────────────────────

    def _copiar(self, texto):
        """Copia texto para a área de transferência."""
        self.root.clipboard_clear()
        self.root.clipboard_append(texto)
        self.status_label.config(text="Código copiado!", foreground=VERDE_SUCESSO)
        self.root.after(2000, lambda: self.status_label.config(
            text=f"Base carregada: {_fmt_num(car_count)} imóveis",
            foreground=VERDE_SUCESSO))

    def _copiar_completo(self, dados):
        """Copia todos os campos do resultado formatados para a área de transferência."""
        linhas = [
            f"Código: {dados.get('cod_imovel', '')}",
            f"Município: {dados.get('municipio', '')}",
            f"Área: {self._fmt_area(dados.get('area_ha', ''))}",
            f"Tipo: {dados.get('tipo', '')}",
            f"Status: {dados.get('status', '')}",
            f"Condição: {dados.get('condicao', '')}",
            f"Mód. Fiscais: {self._fmt_decimal_br(dados.get('modulos_fiscais', ''))}",
        ]
        if dados.get("distancia"):
            linhas.append(f"Distância: {dados['distancia']}")
        linhas.append(f"Coordenada: {self._last_lat:.6f}, {self._last_lon:.6f}")
        texto = "\n".join(linhas)
        self.root.clipboard_clear()
        self.root.clipboard_append(texto)
        self.status_label.config(text="Resultado completo copiado!", foreground=VERDE_SUCESSO)
        self.root.after(2000, lambda: self.status_label.config(
            text=f"Base carregada: {_fmt_num(car_count)} imóveis",
            foreground=VERDE_SUCESSO))

    # ── Ver mapa / Exportar ─────────────────────────────────────────────────

    def _ver_mapa(self, dados=None):
        """Gera mapa HTML com Leaflet e abre no navegador."""
        dados = dados or self._last_resultado
        if not dados or "_geom_idx" not in dados:
            return
        geom = car_geoms[dados["_geom_idx"]]
        html = gerar_mapa_html(geom, self._last_lat, self._last_lon, dados)
        cod = dados.get("cod_imovel", "CAR").replace("/", "_")
        tmp = Path(tempfile.gettempdir()) / f"car_mapa_{cod}.html"
        tmp.write_text(html, encoding="utf-8")
        webbrowser.open(tmp.as_uri())
        self._set_status("Mapa aberto no navegador", VERDE_SUCESSO)

    def _exportar(self, fmt, dados=None):
        """Exporta geometria do resultado como KMZ ou Shapefile."""
        from tkinter import filedialog
        dados = dados or self._last_resultado
        if not dados or "_geom_idx" not in dados:
            return
        geom = car_geoms[dados["_geom_idx"]]
        cod = dados.get("cod_imovel", "CAR").replace("/", "_")

        if fmt == "kmz":
            caminho = filedialog.asksaveasfilename(
                parent=self.root, title="Salvar KMZ",
                initialfile=f"{cod}.kmz", defaultextension=".kmz",
                filetypes=[("Google Earth KMZ", "*.kmz"), ("Todos", "*.*")])
            if not caminho:
                return
            try:
                exportar_kmz(geom, dados, caminho)
                self._set_status(f"KMZ salvo: {Path(caminho).name}", VERDE_SUCESSO)
            except Exception as e:
                log.exception("Erro ao exportar KMZ")
                messagebox.showerror("Erro", f"Falha ao exportar KMZ:\n{e}", parent=self.root)
        elif fmt == "shp":
            caminho = filedialog.asksaveasfilename(
                parent=self.root, title="Salvar Shapefile",
                initialfile=f"{cod}.shp", defaultextension=".shp",
                filetypes=[("Shapefile", "*.shp"), ("Todos", "*.*")])
            if not caminho:
                return
            try:
                exportar_shp(geom, dados, caminho.replace(".shp", ""))
                self._set_status(f"SHP salvo: {Path(caminho).name} (+ .shx, .dbf, .prj)", VERDE_SUCESSO)
            except Exception as e:
                log.exception("Erro ao exportar SHP")
                messagebox.showerror("Erro", f"Falha ao exportar SHP:\n{e}", parent=self.root)

    # ── Consultar (coordenada ou código CAR) ────────────────────────────────

    def on_consultar(self):
        """Dispara consulta por coordenada ou código CAR a partir do campo de entrada."""
        if carregando or car_geoms is None:
            return

        texto = self.entry.get().strip()
        if not texto:
            self._mostrar_erro("Digite uma coordenada ou código CAR")
            return

        # Detectar se é código CAR
        if re.match(r'^[A-Za-z]{2}[-\s]', texto):
            self._buscar_por_codigo(texto)
            return

        lat, lon = parse_coordenada(texto)
        if lat is None or lon is None:
            self._mostrar_erro(
                "Formato não reconhecido.\n\n"
                "Use:\n"
                '  22°03\'12,29" S 42°21\'44,98" W\n'
                "  -22.053414, -42.362494\n"
                "  RJ-3304557-..."
            )
            return

        if lat > 0:
            lat = -lat
        if lon > 0:
            lon = -lon

        if not (-35 <= lat <= 6 and -75 <= lon <= -34):
            self._mostrar_erro(
                "Coordenada fora dos limites do Brasil.\n\n"
                f"Lat: {lat:.6f}  Lon: {lon:.6f}\n"
                "Esperado: Lat [-35, 6] | Lon [-75, -34]"
            )
            return

        self._last_lat = lat
        self._last_lon = lon
        self.status_label.config(text="Consultando...", foreground=CINZA_MEDIO)
        self.btn.config(state="disabled")

        def run():
            try:
                resultados = consultar(lat, lon)
                self.root.after(0, lambda: self._exibir_resultados(resultados))
            except Exception as e:
                log.exception("Erro na consulta")
                err_msg = str(e)
                self.root.after(0, lambda: self._mostrar_erro(f"Erro: {err_msg}"))
            finally:
                self.root.after(0, lambda: self.btn.config(state="normal"))

        threading.Thread(target=run, daemon=True).start()

    # ── Busca por código CAR ────────────────────────────────────────────────

    def _buscar_por_codigo(self, codigo):
        """Busca imóvel pelo código CAR em thread separada."""
        self.status_label.config(text="Buscando código...", foreground=CINZA_MEDIO)
        self.btn.config(state="disabled")

        def run():
            try:
                resultado = consultar_por_codigo(codigo)
                if resultado:
                    geom = car_geoms[resultado["_geom_idx"]]
                    centroid = geom.centroid
                    self._last_lat = centroid.y
                    self._last_lon = centroid.x
                    self.root.after(0, lambda: self._exibir_resultados([resultado]))
                else:
                    self.root.after(0, lambda: self._mostrar_codigo_nao_encontrado(codigo))
            except Exception as e:
                log.exception("Erro na busca por código")
                err_msg = str(e)
                self.root.after(0, lambda: self._mostrar_erro(f"Erro: {err_msg}"))
            finally:
                self.root.after(0, lambda: self.btn.config(state="normal"))

        threading.Thread(target=run, daemon=True).start()

    def _mostrar_codigo_nao_encontrado(self, codigo):
        """Exibe mensagem de código CAR não encontrado na base."""
        self._clear_result()
        ttk.Label(self.result_inner, text="CÓDIGO NÃO ENCONTRADO",
                  font=("Segoe UI", 13, "bold"),
                  foreground=VERMELHO, background=CINZA_BG).pack(expand=True, pady=(30, 5))
        ttk.Label(self.result_inner, text=f"'{codigo}' não existe na base CAR carregada",
                  foreground=CINZA_MEDIO, background=CINZA_BG, font=("Segoe UI", 10)).pack()
        self.status_label.config(text=f"Código não encontrado: {codigo}", foreground=VERMELHO)

    # ── Importar CSV ────────────────────────────────────────────────────────

    def _importar_csv(self):
        """Importa arquivo CSV/TXT para consulta em lote."""
        if carregando or car_geoms is None:
            messagebox.showwarning("Aguarde", "Base CAR ainda carregando...", parent=self.root)
            return

        from tkinter import filedialog
        caminho = filedialog.askopenfilename(
            parent=self.root, title="Importar planilha/CSV",
            filetypes=[("CSV", "*.csv"), ("Texto", "*.txt"), ("Todos", "*.*")])
        if not caminho:
            return

        try:
            import csv
            # Ler arquivo tentando múltiplos encodings
            content = None
            for enc in ["utf-8-sig", "utf-8", "latin-1", "cp1252", "iso-8859-1"]:
                try:
                    with open(caminho, encoding=enc) as f:
                        content = f.read()
                    break
                except (UnicodeDecodeError, UnicodeError):
                    continue

            if content is None:
                messagebox.showerror("Erro", "Não foi possível ler o arquivo.\nTente salvá-lo como UTF-8.", parent=self.root)
                return

            # Auto-detectar delimitador
            first_line = content.split("\n")[0]
            delim = ";"
            for d in [";", "\t", ","]:
                if d in first_line and first_line.count(d) >= 1:
                    delim = d
                    break

            import io
            reader = csv.reader(io.StringIO(content), delimiter=delim)
            all_rows = [row for row in reader if any(cell.strip() for cell in row)]

            if len(all_rows) < 2:
                messagebox.showwarning("Arquivo vazio", "O arquivo não contém dados suficientes.", parent=self.root)
                return

            header = all_rows[0]
            data_rows = all_rows[1:]

            # Auto-detectar colunas de lat/lon pelo nome
            lat_hints = {"lat", "latitude", "y", "lat_y"}
            lon_hints = {"lon", "long", "longitude", "lng", "x", "lon_x"}
            lat_idx = lon_idx = None
            for i, col in enumerate(header):
                col_lower = col.strip().lower()
                if col_lower in lat_hints and lat_idx is None:
                    lat_idx = i
                elif col_lower in lon_hints and lon_idx is None:
                    lon_idx = i

            # Janela de preview com seleção de colunas
            self._csv_preview(header, data_rows, lat_idx, lon_idx)

        except Exception as e:
            messagebox.showerror("Erro", f"Falha ao ler arquivo:\n{e}", parent=self.root)

    def _csv_preview(self, header, data_rows, auto_lat_idx, auto_lon_idx):
        """Mostra preview do CSV e permite selecionar colunas e modo de importação."""
        win = tk.Toplevel(self.root)
        win.title("Importar — Selecionar Colunas")
        win.geometry("700x550")
        win.configure(bg=BRANCO)
        win.grab_set()

        # Ícone
        ico_path = _BASE_DIR / "car.ico"
        try:
            win.iconbitmap(str(ico_path))
        except Exception:
            pass

        ttk.Label(win, text="IMPORTAR DADOS",
                  font=("Segoe UI", 14, "bold"),
                  foreground=VERDE_ESCURO, background=BRANCO).pack(pady=(15, 5))

        ttk.Label(win, text=f"{len(data_rows)} linhas encontradas",
                  font=("Segoe UI", 9),
                  foreground=CINZA_MEDIO, background=BRANCO).pack(pady=(0, 10))

        col_names = [f"{i}: {h.strip()}" for i, h in enumerate(header)]
        NENHUMA = "(nenhuma — coluna única)"

        # Auto-detectar colunas especiais
        auto_car_idx = None
        car_hints = {"cod_imovel", "car", "codigo", "código", "cod", "codigo_car", "código_car"}
        coord_single_hints = {"coordenada", "coord", "coordenadas", "coords", "ponto", "gms"}
        auto_coord_idx = None
        for i, col in enumerate(header):
            col_lower = col.strip().lower()
            if col_lower in car_hints and auto_car_idx is None:
                auto_car_idx = i
            if col_lower in coord_single_hints and auto_coord_idx is None:
                auto_coord_idx = i

        # ── Estilos do combobox ──
        style = ttk.Style()
        style.configure("Import.TCombobox", padding=6)
        style.configure("ImportLabel.TLabel", background=BRANCO, foreground=CINZA_TEXTO,
                        font=("Segoe UI", 10))

        # ── Modo de importação (tabs estilizados) ──
        mode_var = tk.StringVar(value="coords")
        mode_frame = tk.Frame(win, bg=BRANCO)
        mode_frame.pack(fill="x", padx=20, pady=(0, 12))

        tab_btns = {}

        def _set_tab_style():
            for val, btn in tab_btns.items():
                if val == mode_var.get():
                    btn.configure(bg=VERDE_ESCURO, fg=BRANCO)
                else:
                    btn.configure(bg=CINZA_CLARO, fg=CINZA_TEXTO)

        def _select_tab(val):
            mode_var.set(val)
            _set_tab_style()
            on_mode_change()

        for val, text in [("coords", "Por Coordenadas"), ("car", "Por Código CAR")]:
            b = tk.Button(mode_frame, text=text,
                          font=("Segoe UI", 10, "bold"),
                          relief="flat", bd=0, padx=20, pady=6, cursor="hand2",
                          command=lambda v=val: _select_tab(v))
            b.pack(side="left", padx=(0, 4))
            tab_btns[val] = b

        _set_tab_style()

        lat_var = tk.StringVar(value=col_names[auto_lat_idx] if auto_lat_idx is not None else
                               (col_names[auto_coord_idx] if auto_coord_idx is not None else ""))
        lon_var = tk.StringVar(value=col_names[auto_lon_idx] if auto_lon_idx is not None else NENHUMA)
        car_var = tk.StringVar(value=col_names[auto_car_idx] if auto_car_idx is not None else "")

        def on_mode_change(*_):
            for w in sel_frame.winfo_children():
                w.destroy()

            if mode_var.get() == "coords":
                r0 = tk.Frame(sel_frame, bg=BRANCO)
                r0.pack(fill="x", pady=4)
                tk.Label(r0, text="Latitude:", font=("Segoe UI", 10),
                         bg=BRANCO, fg=VERDE_ESCURO, width=12, anchor="e").pack(side="left", padx=(0, 8))
                ttk.Combobox(r0, textvariable=lat_var, values=col_names,
                             state="readonly", width=35, style="Import.TCombobox").pack(side="left")

                r1 = tk.Frame(sel_frame, bg=BRANCO)
                r1.pack(fill="x", pady=4)
                tk.Label(r1, text="Longitude:", font=("Segoe UI", 10),
                         bg=BRANCO, fg=VERDE_ESCURO, width=12, anchor="e").pack(side="left", padx=(0, 8))
                ttk.Combobox(r1, textvariable=lon_var, values=[NENHUMA] + col_names,
                             state="readonly", width=35, style="Import.TCombobox").pack(side="left")

                tk.Label(sel_frame,
                         text="Coluna única com lat+lon? Deixe longitude como \"coluna única\".\n"
                              "Aceita GMS, decimal e formatos mistos.",
                         font=("Segoe UI", 8), bg=BRANCO, fg=CINZA_MEDIO,
                         justify="left").pack(anchor="w", pady=(2, 0))

            elif mode_var.get() == "car":
                r0 = tk.Frame(sel_frame, bg=BRANCO)
                r0.pack(fill="x", pady=4)
                tk.Label(r0, text="Código CAR:", font=("Segoe UI", 10),
                         bg=BRANCO, fg=VERDE_ESCURO, width=12, anchor="e").pack(side="left", padx=(0, 8))
                ttk.Combobox(r0, textvariable=car_var, values=col_names,
                             state="readonly", width=35, style="Import.TCombobox").pack(side="left")

        # ── Seleção de colunas (dinâmico) ──
        sel_frame = tk.Frame(win, bg=BRANCO)
        sel_frame.pack(fill="x", padx=20, pady=(0, 10))

        on_mode_change()

        # ── Preview da tabela ──
        tk.Frame(win, bg=BORDA, height=1).pack(fill="x", padx=20, pady=5)

        ttk.Label(win, text="Preview (primeiras 10 linhas):",
                  font=("Segoe UI", 9), foreground=CINZA_MEDIO, background=BRANCO).pack(anchor="w", padx=20)

        preview_frame = tk.Frame(win, bg=BRANCO)
        preview_frame.pack(fill="both", expand=True, padx=20, pady=(5, 10))

        for j, h in enumerate(header[:8]):
            tk.Label(preview_frame, text=h.strip()[:18], font=("Consolas", 8, "bold"),
                     bg=CINZA_CLARO, fg=CINZA_TEXTO, padx=5, pady=3,
                     relief="solid", bd=1).grid(row=0, column=j, sticky="nsew")

        for i, row in enumerate(data_rows[:10]):
            for j, val in enumerate(row[:8]):
                tk.Label(preview_frame, text=val.strip()[:18], font=("Consolas", 8),
                         bg=BRANCO, fg=CINZA_TEXTO, padx=5, pady=2,
                         relief="solid", bd=1).grid(row=i+1, column=j, sticky="nsew")

        # ── Confirmar ──
        def confirmar():
            modo = mode_var.get()
            win.destroy()

            if modo == "car":
                car_sel = car_var.get()
                if not car_sel or car_sel == NENHUMA:
                    messagebox.showwarning("Selecione", "Selecione a coluna de código CAR.", parent=self.root)
                    return
                car_i = int(car_sel.split(":")[0])
                codigos = []
                for row in data_rows:
                    if len(row) > car_i and row[car_i].strip():
                        codigos.append(row[car_i].strip())
                if not codigos:
                    messagebox.showwarning("Sem dados", "Nenhum código encontrado na coluna selecionada.", parent=self.root)
                    return
                self._processar_lote_car(codigos)
                return

            # Modo coordenadas
            lat_sel = lat_var.get()
            lon_sel = lon_var.get()
            if not lat_sel or lat_sel == NENHUMA:
                messagebox.showwarning("Selecione", "Selecione pelo menos a coluna de latitude/coordenada.", parent=self.root)
                return

            lat_i = int(lat_sel.split(":")[0])
            coluna_unica = (lon_sel == NENHUMA or not lon_sel)
            lon_i = None if coluna_unica else int(lon_sel.split(":")[0])

            coordenadas = []
            for row in data_rows:
                try:
                    if coluna_unica:
                        # Coluna única: pode ser DMS, decimal com separador, etc.
                        if len(row) <= lat_i:
                            continue
                        texto = row[lat_i].strip()
                        if not texto:
                            continue
                        lat, lon = parse_coordenada(texto)
                        if lat is None or lon is None:
                            continue
                    else:
                        if len(row) <= max(lat_i, lon_i):
                            continue
                        lat_txt = row[lat_i].strip()
                        lon_txt = row[lon_i].strip()
                        if not lat_txt or not lon_txt:
                            continue
                        # Tentar decimal direto
                        try:
                            lat = float(lat_txt.replace(",", "."))
                            lon = float(lon_txt.replace(",", "."))
                        except ValueError:
                            # Tentar DMS em cada coluna
                            lat = parse_dms(lat_txt)
                            lon = parse_dms(lon_txt)
                            if lat is None or lon is None:
                                continue

                    if lat > 0:
                        lat = -lat
                    if lon > 0:
                        lon = -lon
                    coordenadas.append((lat, lon))
                except (ValueError, IndexError):
                    continue

            if not coordenadas:
                messagebox.showwarning("Sem dados",
                    "Nenhuma coordenada válida encontrada nas colunas selecionadas.",
                    parent=self.root)
                return

            self._set_status(f"Processando {len(coordenadas)} coordenadas...", CINZA_MEDIO)
            self.btn.config(state="disabled")

            def run():
                try:
                    resultados = consulta_lote(coordenadas)
                    self.root.after(0, lambda: self._exibir_lote(resultados))
                except Exception as e:
                    log.exception("Erro na consulta em lote")
                    err_msg = str(e)
                    self.root.after(0, lambda: self._mostrar_erro(f"Erro: {err_msg}"))
                finally:
                    self.root.after(0, lambda: self.btn.config(state="normal"))

            threading.Thread(target=run, daemon=True).start()

        btn_frame = tk.Frame(win, bg=BRANCO)
        btn_frame.pack(pady=(0, 15))

        tk.Button(btn_frame, text="PROCESSAR",
                  font=("Segoe UI", 11, "bold"),
                  bg=VERDE_ESCURO, fg=BRANCO,
                  activebackground=VERDE_HOVER, activeforeground=BRANCO,
                  relief="flat", bd=0, padx=25, pady=8, cursor="hand2",
                  command=confirmar).pack(side="left", padx=(0, 10))

        tk.Button(btn_frame, text="Cancelar",
                  font=("Segoe UI", 9),
                  bg=CINZA_CLARO, fg=CINZA_TEXTO,
                  relief="flat", bd=0, padx=15, pady=8, cursor="hand2",
                  command=win.destroy).pack(side="left")

    def _processar_lote_car(self, codigos):
        """Processa lista de códigos CAR."""
        self._set_status(f"Buscando {len(codigos)} códigos CAR...", CINZA_MEDIO)
        self.btn.config(state="disabled")

        def run():
            resultados = []
            for cod in codigos:
                r = consultar_por_codigo(cod)
                if r:
                    geom = car_geoms[r["_geom_idx"]]
                    c = geom.centroid
                    resultados.append({"lat": c.y, "lon": c.x, "resultados": [r]})
                else:
                    resultados.append({"lat": 0, "lon": 0, "resultados": [], "codigo": cod})

            self.root.after(0, lambda: self._exibir_lote(resultados))
            self.root.after(0, lambda: self.btn.config(state="normal"))

        threading.Thread(target=run, daemon=True).start()

    def _exibir_lote(self, resultados):
        """Exibe resumo dos resultados da consulta em lote no painel."""
        self._clear_result()

        encontrados = sum(1 for r in resultados if r["resultados"])
        total = len(resultados)

        ttk.Label(self.result_inner, text="CONSULTA EM LOTE",
                  font=("Segoe UI", 14, "bold"),
                  foreground=VERDE_ESCURO, background=CINZA_BG).pack(pady=(10, 5))

        ttk.Label(self.result_inner,
                  text=f"{encontrados} de {total} coordenadas com CAR encontrado",
                  font=("Segoe UI", 11),
                  foreground=CINZA_TEXTO, background=CINZA_BG).pack(pady=(0, 10))

        tk.Frame(self.result_inner, bg=BORDA, height=1).pack(fill="x", pady=5)

        for i, r in enumerate(resultados[:20]):
            row = ttk.Frame(self.result_inner, style="Card.TFrame")
            row.pack(fill="x", pady=2)

            coord_txt = f"{r['lat']:.6f}, {r['lon']:.6f}"
            if r["resultados"]:
                cod = r["resultados"][0].get("cod_imovel", "?")
                mun = r["resultados"][0].get("municipio", "")
                n_extra = f" (+{len(r['resultados'])-1})" if len(r["resultados"]) > 1 else ""
                ttk.Label(row, text=coord_txt, font=("Consolas", 8),
                          foreground=CINZA_MEDIO, background=CINZA_BG).pack(side="left")
                ttk.Label(row, text=f"  {cod}{n_extra} — {mun}",
                          font=("Segoe UI", 9, "bold"),
                          foreground=VERDE_ESCURO, background=CINZA_BG).pack(side="left")
            else:
                ttk.Label(row, text=coord_txt, font=("Consolas", 8),
                          foreground=CINZA_MEDIO, background=CINZA_BG).pack(side="left")
                ttk.Label(row, text="  Não encontrado",
                          font=("Segoe UI", 9),
                          foreground=VERMELHO, background=CINZA_BG).pack(side="left")

        if total > 20:
            ttk.Label(self.result_inner, text=f"... e mais {total - 20} resultados",
                      font=("Segoe UI", 9), foreground=CINZA_MEDIO, background=CINZA_BG).pack(pady=5)

        action_frame = ttk.Frame(self.result_inner, style="Card.TFrame")
        action_frame.pack(fill="x", pady=(15, 5))

        tk.Button(action_frame, text="EXPORTAR RESULTADO (CSV)",
                  font=("Segoe UI", 10, "bold"),
                  bg=VERDE_ESCURO, fg=BRANCO,
                  activebackground=VERDE_HOVER, activeforeground=BRANCO,
                  relief="flat", bd=0, padx=20, pady=8, cursor="hand2",
                  command=lambda: self._exportar_lote_csv(resultados)).pack()

        self._set_status(f"Lote: {encontrados}/{total} encontrados", VERDE_SUCESSO)

    def _exportar_lote_csv(self, resultados):
        """Exporta resultados da consulta em lote para arquivo CSV."""
        from tkinter import filedialog
        import csv

        caminho = filedialog.asksaveasfilename(
            parent=self.root, title="Salvar resultado",
            initialfile="resultado_lote.csv", defaultextension=".csv",
            filetypes=[("CSV", "*.csv"), ("Todos", "*.*")])
        if not caminho:
            return

        try:
            with open(caminho, "w", newline="", encoding="utf-8-sig") as f:
                writer = csv.writer(f, delimiter=";")
                writer.writerow(["latitude", "longitude", "cod_imovel", "municipio",
                                 "area_ha", "tipo", "status", "condicao", "distancia", "observacao"])
                for r in resultados:
                    if r["resultados"]:
                        for res in r["resultados"]:
                            writer.writerow([
                                f"{r['lat']:.6f}", f"{r['lon']:.6f}",
                                res.get("cod_imovel", ""), res.get("municipio", ""),
                                res.get("area_ha", ""), res.get("tipo", ""),
                                res.get("status", ""), res.get("condicao", ""),
                                res.get("distancia", ""), res.get("observacao", ""),
                            ])
                    else:
                        writer.writerow([f"{r['lat']:.6f}", f"{r['lon']:.6f}",
                                         "", "", "", "", "", "", "", "Não encontrado"])

            self._set_status(f"CSV salvo: {Path(caminho).name}", VERDE_SUCESSO)
        except Exception as e:
            messagebox.showerror("Erro", f"Falha ao exportar CSV:\n{e}", parent=self.root)

    # ── Histórico ───────────────────────────────────────────────────────────

    def _mostrar_historico(self):
        """Abre janela com histórico de consultas e opção de re-consultar."""
        hist = carregar_historico()
        if not hist:
            messagebox.showinfo("Histórico", "Nenhuma consulta realizada ainda.", parent=self.root)
            return

        win = tk.Toplevel(self.root)
        win.title("Histórico de Consultas")
        win.geometry("700x450")
        win.configure(bg=BRANCO)
        try:
            win.iconbitmap(str(_BASE_DIR / "car.ico"))
        except Exception:
            pass

        ttk.Label(win, text="HISTÓRICO DE CONSULTAS",
                  font=("Segoe UI", 14, "bold"),
                  foreground=VERDE_ESCURO, background=BRANCO).pack(pady=(15, 10))

        container = tk.Frame(win, bg=BRANCO)
        container.pack(fill="both", expand=True, padx=15, pady=(0, 10))

        canvas = tk.Canvas(container, bg=BRANCO, highlightthickness=0)
        scrollbar = ttk.Scrollbar(container, orient="vertical", command=canvas.yview)
        scroll_frame = ttk.Frame(canvas, style="TFrame")

        scroll_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        canvas.bind("<Enter>", lambda e: canvas.bind_all("<MouseWheel>",
            lambda ev: canvas.yview_scroll(-1 * (ev.delta // 120), "units")))
        canvas.bind("<Leave>", lambda e: canvas.unbind_all("<MouseWheel>"))

        for item in hist:
            row = tk.Frame(scroll_frame, bg=CINZA_BG, padx=10, pady=5)
            row.pack(fill="x", pady=2)

            info = f"{item['data']}  |  {item['lat']:.6f}, {item['lon']:.6f}"
            tk.Label(row, text=info, font=("Consolas", 8), bg=CINZA_BG, fg=CINZA_MEDIO).pack(anchor="w")

            cod = item.get("cod_imovel", "")
            mun = item.get("municipio", "")
            if cod:
                tk.Label(row, text=f"{cod} — {mun}",
                         font=("Segoe UI", 10, "bold"), bg=CINZA_BG, fg=VERDE_ESCURO).pack(anchor="w")
            else:
                tk.Label(row, text="Não encontrado",
                         font=("Segoe UI", 10), bg=CINZA_BG, fg=VERMELHO).pack(anchor="w")

            lat, lon = item["lat"], item["lon"]
            tk.Button(row, text="Re-consultar",
                      font=("Segoe UI", 8), bg=VERDE_MEDIO, fg=BRANCO,
                      relief="flat", bd=0, padx=8, pady=2, cursor="hand2",
                      command=lambda la=lat, lo=lon, w=win: (
                          w.destroy(),
                          self.entry.delete(0, tk.END),
                          self.entry.insert(0, f"{la:.6f}, {lo:.6f}"),
                          self.on_consultar(),
                      )).pack(anchor="e")

        btn_frame = tk.Frame(win, bg=BRANCO)
        btn_frame.pack(pady=(0, 15))
        tk.Button(btn_frame, text="Limpar Histórico",
                  font=("Segoe UI", 9), bg=VERMELHO, fg=BRANCO,
                  relief="flat", bd=0, padx=15, pady=5, cursor="hand2",
                  command=lambda: (limpar_historico(), win.destroy(),
                                   messagebox.showinfo("Histórico", "Histórico limpo.", parent=self.root))
                  ).pack()

    # ── Atualizar base ──────────────────────────────────────────────────────

    def on_atualizar(self):
        """Inicia download da base CAR via WFS em thread separada."""
        global atualizando
        if atualizando:
            return

        if not messagebox.askyesno(
            "Atualizar Base CAR",
            "Isso vai baixar todos os imóveis CAR do RJ direto do\n"
            "GeoServer do SICAR (geoserver.car.gov.br).\n\n"
            "São ~67.000 imóveis — pode levar alguns minutos.\n"
            "A base atual será salva como backup.\n\n"
            "Deseja continuar?",
            parent=self.root,
        ):
            return

        atualizando = True
        self.cancel_update = False
        self.btn.config(state="disabled")
        self.btn_atualizar.config(state="disabled")

        self.progress["value"] = 0
        self.progress_frame.pack(padx=30, pady=(5, 0), before=self.result_frame)

        def progress_cb(msg):
            pct = 0
            if "%" in msg:
                try:
                    pct = int(msg.split("(")[1].split("%")[0])
                except (IndexError, ValueError):
                    pass
            self.root.after(0, lambda: (
                self._set_status(msg, VERDE_MEDIO),
                setattr(self.progress, "value", None) or self.progress.configure(value=pct),
            ))

        def run_update():
            global atualizando
            try:
                total = baixar_wfs(
                    progress_callback=progress_cb,
                    cancel_check=lambda: self.cancel_update,
                )

                if total is None:
                    self.root.after(0, lambda: self._set_status("Atualização cancelada", VERMELHO))
                    return

                self.root.after(0, lambda: (
                    self._set_status("Recarregando base...", CINZA_MEDIO),
                    self.progress.configure(value=98),
                ))

                count = _load_car_from_gpkg()

                info_path = PASTA_DADOS / "atualizacao.txt"
                data_info = f" (atualizado em {info_path.read_text().strip()})" if info_path.exists() else ""

                def show_success():
                    self.progress.configure(value=100)
                    self._set_status(
                        f"Base atualizada: {_fmt_num(count)} imóveis{data_info}",
                        VERDE_SUCESSO,
                    )
                    self.lbl_data_atualizacao.config(text=self._get_data_atualizacao())
                    messagebox.showinfo(
                        "Atualização concluída",
                        f"Base CAR atualizada com sucesso!\n\n"
                        f"Total: {_fmt_num(count)} imóveis\n"
                        f"Data: {datetime.now().strftime('%d/%m/%Y %H:%M')}",
                        parent=self.root,
                    )

                self.root.after(0, show_success)

            except Exception as e:
                log.exception("Erro ao atualizar via WFS")
                err_msg = str(e)
                self.root.after(0, lambda: self._set_status(f"Erro: {err_msg}", VERMELHO))
                self.root.after(0, lambda: messagebox.showerror(
                    "Erro", f"Falha ao atualizar:\n{err_msg}", parent=self.root))
            finally:
                atualizando = False
                def cleanup():
                    self.progress_frame.pack_forget()
                    self.btn_atualizar.config(state="normal")
                    if car_geoms is not None:
                        self.btn.config(state="normal")
                self.root.after(0, cleanup)

        threading.Thread(target=run_update, daemon=True).start()


# ── Mapa e exportação ─────────────────────────────────────────────────────────

def _geom_coords_leaflet(geom):
    """Extrai coordenadas de um polígono/multipolígono para formato Leaflet [[lat,lon],...]."""
    from shapely.geometry import MultiPolygon, Polygon
    polygons = []
    if isinstance(geom, MultiPolygon):
        parts = list(geom.geoms)
    elif isinstance(geom, Polygon):
        parts = [geom]
    else:
        return []
    for poly in parts:
        ring = [[y, x] for x, y in poly.exterior.coords]
        polygons.append(ring)
    return polygons


def gerar_mapa_html(geom, lat, lon, dados):
    """Gera HTML com Leaflet mostrando polígono CAR sobre satélite."""
    import html as html_mod
    coords = _geom_coords_leaflet(geom)
    cod = html_mod.escape(str(dados.get("cod_imovel", "CAR")))
    municipio = html_mod.escape(str(dados.get("municipio", "")))
    area = html_mod.escape(str(dados.get("area_ha", "")))

    # Centro no centroid do polígono
    centroid = geom.centroid
    clat, clon = centroid.y, centroid.x

    # Bounds para zoom automático
    bounds = geom.bounds  # (minx, miny, maxx, maxy)

    popup_text = f"<b>{cod}</b><br>{municipio}"
    if area:
        popup_text += f"<br>{area} ha"

    html = f"""<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>CAR — {cod}</title>
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css"/>
<script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
<style>
  body {{ margin:0; padding:0; }}
  #map {{ width:100%; height:100vh; }}
  .info-box {{
    background: rgba(255,255,255,0.92); padding: 12px 16px;
    border-radius: 8px; box-shadow: 0 2px 8px rgba(0,0,0,0.3);
    font-family: 'Segoe UI', Arial, sans-serif; font-size: 13px;
    line-height: 1.6; max-width: 340px;
  }}
  .info-box b {{ color: #006634; font-size: 14px; }}
</style>
</head>
<body>
<div id="map"></div>
<script>
var map = L.map('map');

// Camadas base
var satelite = L.tileLayer(
  'https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{{z}}/{{y}}/{{x}}',
  {{attribution: 'Esri World Imagery', maxZoom: 19}}
).addTo(map);

var osm = L.tileLayer(
  'https://{{s}}.tile.openstreetmap.org/{{z}}/{{y}}/{{x}}.png',
  {{attribution: '&copy; OpenStreetMap', maxZoom: 19}}
);

var labels = L.tileLayer(
  'https://server.arcgisonline.com/ArcGIS/rest/services/Reference/World_Boundaries_and_Places/MapServer/tile/{{z}}/{{y}}/{{x}}',
  {{maxZoom: 19, opacity: 0.9}}
).addTo(map);

L.control.layers(
  {{"Satélite": satelite, "OpenStreetMap": osm}},
  {{"Rótulos": labels}},
  {{position: 'topright'}}
).addTo(map);

// Polígono CAR
var coords = {json.dumps(coords)};
var polygons = [];
for (var i = 0; i < coords.length; i++) {{
  var poly = L.polygon(coords[i], {{
    color: '#FFD700', weight: 3, fillColor: '#FFD700', fillOpacity: 0.25
  }});
  poly.bindPopup('{popup_text}');
  polygons.push(poly);
}}
var carGroup = L.featureGroup(polygons).addTo(map);

// Pin da consulta
L.marker([{lat}, {lon}], {{
  title: 'Ponto consultado'
}}).addTo(map).bindPopup('Coordenada consultada<br>{lat:.6f}, {lon:.6f}');

// Zoom no polígono
map.fitBounds(carGroup.getBounds().pad(0.3));

// Info box
var info = L.control({{position: 'bottomleft'}});
info.onAdd = function() {{
  var div = L.DomUtil.create('div', 'info-box');
  div.innerHTML = '<b>{cod}</b><br>Município: {municipio}<br>Área: {area} ha';
  return div;
}};
info.addTo(map);
</script>
</body>
</html>"""
    return html


def exportar_kmz(geom, dados, caminho):
    """Exporta polígono CAR como KMZ (KML zipado)."""
    from shapely.geometry import MultiPolygon, Polygon
    cod = dados.get("cod_imovel", "CAR")
    municipio = dados.get("municipio", "")
    area = dados.get("area_ha", "")

    if isinstance(geom, MultiPolygon):
        parts = list(geom.geoms)
    elif isinstance(geom, Polygon):
        parts = [geom]
    else:
        parts = []

    placemark_coords = ""
    for poly in parts:
        ring_str = " ".join(f"{x},{y},0" for x, y in poly.exterior.coords)
        placemark_coords += f"""
      <Placemark>
        <name>{cod}</name>
        <description>Município: {municipio} — Área: {area} ha</description>
        <Style>
          <LineStyle><color>ff00d7ff</color><width>3</width></LineStyle>
          <PolyStyle><color>4000d7ff</color></PolyStyle>
        </Style>
        <Polygon>
          <outerBoundaryIs><LinearRing>
            <coordinates>{ring_str}</coordinates>
          </LinearRing></outerBoundaryIs>
        </Polygon>
      </Placemark>"""

    kml = f"""<?xml version="1.0" encoding="UTF-8"?>
<kml xmlns="http://www.opengis.net/kml/2.2">
<Document>
  <name>CAR — {cod}</name>
  <description>Cadastro Ambiental Rural — {municipio}</description>
  {placemark_coords}
</Document>
</kml>"""

    with zipfile.ZipFile(caminho, "w", zipfile.ZIP_DEFLATED) as zf:
        zf.writestr("doc.kml", kml)
    log.info("KMZ exportado: %s", caminho)


def exportar_shp(geom, dados, caminho_base):
    """Exporta polígono CAR como Shapefile (.shp/.shx/.dbf/.prj) usando escrita binária."""
    from shapely.geometry import MultiPolygon, Polygon
    cod = dados.get("cod_imovel", "CAR")
    municipio = dados.get("municipio", "")
    area_str = dados.get("area_ha", "0")

    if isinstance(geom, MultiPolygon):
        parts = list(geom.geoms)
    elif isinstance(geom, Polygon):
        parts = [geom]
    else:
        parts = []

    # ── .prj (WGS84 / SIRGAS 2000 compat) ──
    prj = (
        'GEOGCS["GCS_SIRGAS_2000",'
        'DATUM["D_SIRGAS_2000",'
        'SPHEROID["GRS_1980",6378137.0,298.257222101]],'
        'PRIMEM["Greenwich",0.0],'
        'UNIT["Degree",0.0174532925199433]]'
    )
    Path(caminho_base + ".prj").write_text(prj, encoding="utf-8")

    # Preparar coordenadas e bounds
    all_parts_coords = []
    all_x, all_y = [], []
    for poly in parts:
        coords = list(poly.exterior.coords)
        all_parts_coords.append(coords)
        for x, y in coords:
            all_x.append(x)
            all_y.append(y)

    bbox = (min(all_x), min(all_y), max(all_x), max(all_y))
    num_parts = len(all_parts_coords)
    total_points = sum(len(c) for c in all_parts_coords)

    # Shape type 5 = Polygon
    # Content length in 16-bit words
    # Record content: shape_type(4) + bbox(32) + num_parts(4) + num_points(4) + parts_index(num_parts*4) + points(total_points*16)
    rec_content_bytes = 4 + 32 + 4 + 4 + num_parts * 4 + total_points * 16
    rec_content_words = rec_content_bytes // 2

    # ── .shp ──
    shp_buf = bytearray()
    # File header: 100 bytes
    file_len_words = (100 + 8 + rec_content_bytes) // 2
    # Bytes 0-3: file code 9994 (big-endian)
    shp_buf += struct.pack(">I", 9994)
    # Bytes 4-23: unused
    shp_buf += b'\x00' * 20
    # Bytes 24-27: file length in 16-bit words (big-endian)
    shp_buf += struct.pack(">I", file_len_words)
    # Bytes 28-31: version 1000 (little-endian)
    shp_buf += struct.pack("<I", 1000)
    # Bytes 32-35: shape type 5 (polygon)
    shp_buf += struct.pack("<I", 5)
    # Bytes 36-67: bounding box (xmin, ymin, xmax, ymax as doubles LE)
    shp_buf += struct.pack("<dddd", *bbox)
    # Bytes 68-83: Zmin, Zmax (0)
    shp_buf += struct.pack("<dd", 0.0, 0.0)
    # Bytes 84-99: Mmin, Mmax (0)
    shp_buf += struct.pack("<dd", 0.0, 0.0)
    # Record header (big-endian): record_number, content_length
    shp_buf += struct.pack(">II", 1, rec_content_words)
    # Record content
    shp_buf += struct.pack("<I", 5)  # shape type
    shp_buf += struct.pack("<dddd", *bbox)
    shp_buf += struct.pack("<I", num_parts)
    shp_buf += struct.pack("<I", total_points)
    # Part indices
    offset = 0
    for pc in all_parts_coords:
        shp_buf += struct.pack("<I", offset)
        offset += len(pc)
    # Points
    for pc in all_parts_coords:
        for x, y in pc:
            shp_buf += struct.pack("<dd", x, y)

    Path(caminho_base + ".shp").write_bytes(bytes(shp_buf))

    # ── .shx ──
    shx_buf = bytearray()
    shx_file_len = (100 + 8) // 2
    shx_buf += struct.pack(">I", 9994)
    shx_buf += b'\x00' * 20
    shx_buf += struct.pack(">I", shx_file_len)
    shx_buf += struct.pack("<I", 1000)
    shx_buf += struct.pack("<I", 5)
    shx_buf += struct.pack("<dddd", *bbox)
    shx_buf += struct.pack("<dd", 0.0, 0.0)
    shx_buf += struct.pack("<dd", 0.0, 0.0)
    # Record: offset=50 (100 bytes / 2), content_length
    shx_buf += struct.pack(">II", 50, rec_content_words)

    Path(caminho_base + ".shx").write_bytes(bytes(shx_buf))

    # ── .dbf (dBASE III) ──
    dbf_buf = bytearray()
    # Header
    fields = [
        ("COD_IMOVEL", "C", 60, cod),
        ("MUNICIPIO", "C", 60, municipio),
        ("AREA_HA", "C", 20, area_str),
    ]
    num_fields = len(fields)
    header_size = 32 + num_fields * 32 + 1
    record_size = 1 + sum(f[2] for f in fields)

    dbf_buf += struct.pack("<B", 3)  # version
    dbf_buf += struct.pack("<BBB", 26, 4, 1)  # date YY MM DD
    dbf_buf += struct.pack("<I", 1)  # num records
    dbf_buf += struct.pack("<H", header_size)
    dbf_buf += struct.pack("<H", record_size)
    dbf_buf += b'\x00' * 20  # reserved

    for fname, ftype, fsize, _ in fields:
        dbf_buf += fname.encode("ascii").ljust(11, b'\x00')
        dbf_buf += ftype.encode("ascii")
        dbf_buf += b'\x00' * 4  # reserved
        dbf_buf += struct.pack("<B", fsize)
        dbf_buf += b'\x00' * 15

    dbf_buf += b'\r'  # header terminator

    # Record
    dbf_buf += b' '  # deletion flag
    for fname, ftype, fsize, fval in fields:
        dbf_buf += fval[:fsize].encode("latin-1", errors="replace").ljust(fsize, b' ')

    dbf_buf += b'\x1a'  # EOF

    Path(caminho_base + ".dbf").write_bytes(bytes(dbf_buf))

    log.info("SHP exportado: %s.*", caminho_base)


def main():
    root = tk.Tk()
    root.iconname("Consulta CAR")
    ico_path = _BASE_DIR / "car.ico"
    try:
        root.iconbitmap(str(ico_path))
    except Exception:
        pass
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
