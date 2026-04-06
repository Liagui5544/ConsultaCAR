<div align="center">

# ConsultaCAR

**Ferramenta desktop para consulta de imóveis do Cadastro Ambiental Rural (CAR)**

[![Python 3.12](https://img.shields.io/badge/Python-3.12-3776AB?logo=python&logoColor=white)](https://python.org)
[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](LICENSE)
[![Platform: Windows](https://img.shields.io/badge/Platform-Windows-0078D6?logo=windows&logoColor=white)](#requisitos)

Localiza propriedades rurais cadastradas no [SICAR](https://www.car.gov.br/) a partir de **coordenadas geográficas** ou **códigos CAR**, com base local de ~67.000 imóveis e busca espacial O(log N).

</div>

---

## Destaques

- Consultas **100% offline** — sem dependência de servidor
- Índice espacial **STRtree** sobre ~67k polígonos
- Aceita **qualquer formato** de coordenada (decimal, GMS, vírgula BR)
- Importação em lote via **CSV** com detecção automática de colunas
- Mapa embutido com **satélite** + mapa interativo **Leaflet** no navegador
- Exportação **KMZ** (Google Earth) e **Shapefile** (QGIS/ArcGIS)
- Atualização da base via **WFS** direto do GeoServer do SICAR
- Executável portátil — **sem instalação**

---

## Screenshot

> *Em breve*

---

## Como Funciona

```
consulta_car_ui.py          ← Arquivo único com toda a lógica
  │
  ├── GeoPackage (SQLite)   ← Base de dados espacial local
  ├── Shapely STRtree       ← Índice espacial O(log N)
  ├── tkinter / ttk         ← Interface gráfica
  ├── tkintermapview         ← Mapa embutido (Esri Satellite)
  ├── Leaflet (HTML)        ← Mapa interativo no navegador
  └── WFS (urllib)          ← Download/atualização da base
```

### Fluxo de consulta

1. **Carregamento** — GPKG é lido via `sqlite3`, geometrias convertidas de WKB com `shapely.from_wkb()`, indexadas em `STRtree`
2. **Busca** — `STRtree.query(point, predicate="intersects")` encontra imóveis que contêm o ponto
3. **Fallback** — Se nenhum hit, `STRtree.nearest()` + Haversine até 500m
4. **Código CAR** — Lookup O(1) via dicionário `cod_imovel → índice`

---

## Estrutura do Projeto

```
ConsultaCAR/
├── consulta_car_ui.py      Aplicação principal (~2400 linhas)
├── CONSULTAR_CAR.vbs       Launcher Windows (detecta Python automaticamente)
├── car.ico                 Ícone da aplicação
├── requirements.txt        Dependências Python
├── build.bat               Script de build (PyInstaller)
├── LICENSE                 GPL-3.0
└── dados/                  Criada automaticamente na primeira execução
    ├── car_rj.gpkg         Base CAR (baixada via "Atualizar Base")
    ├── atualizacao.txt     Data da última atualização
    └── historico.db        Histórico de consultas
```

---

## Instalação (desenvolvimento)

```bash
# Clone
git clone https://github.com/Furiatii/ConsultaCAR.git
cd ConsultaCAR

# Ambiente virtual
python -m venv .venv
.venv\Scripts\activate

# Dependências
pip install -r requirements.txt

# Executar
python consulta_car_ui.py
```

> Na primeira execução, clique em **"Atualizar Base"** para baixar os dados do SICAR.

---

## Build (executável)

```bash
pip install pyinstaller
build.bat
```

O executável é gerado em `dist/Consulta CAR/`.

---

## Formatos de Coordenada

| Formato | Exemplo |
|---------|---------|
| Decimal | `-22.053414, -42.362494` |
| Ponto-e-vírgula | `-22.053414; -42.362494` |
| Vírgula BR | `-22,053414; -42,362494` |
| GMS | `22°03'12,29" S 42°21'44,98" W` |

---

## Stack Técnica

| Componente | Tecnologia |
|---|---|
| Linguagem | Python 3.12 |
| Interface | tkinter / ttk |
| Índice espacial | Shapely STRtree |
| Base de dados | GeoPackage (SQLite + WKB) |
| Mapa embutido | tkintermapview |
| Mapa interativo | Leaflet.js |
| Download de dados | WFS (geoserver.car.gov.br) |
| Build | PyInstaller |

---

## Funcionalidades

| Funcionalidade | Descrição |
|---|---|
| Consulta por coordenada | Busca espacial com múltiplos resultados |
| Consulta por código CAR | Lookup O(1) por código do imóvel |
| Importação CSV | Lote com preview, seleção de colunas e detecção automática |
| Mapa embutido | Polígonos coloridos sobre satélite |
| Mapa Leaflet | Abre no navegador com camadas e popups |
| Exportação KMZ | Para Google Earth |
| Exportação SHP | Para QGIS e ArcGIS |
| Exportação CSV | Resultado de consultas em lote |
| Histórico | 500 últimas consultas com re-consulta |
| Atualização WFS | Download paralelo com retry e backup automático |

---

## Requisitos

| | |
|---|---|
| **Executar (dev)** | Python 3.12+, Windows / Linux |
| **Executar (.exe)** | Windows 10/11 |
| **Internet** | Apenas para tiles do mapa e atualização da base |

---

## Licença

[GPL-3.0](LICENSE)

---

<div align="center">

Desenvolvido por **Gabriel Furiati**

</div>
