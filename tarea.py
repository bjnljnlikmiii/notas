#!/usr/bin/env python3
"""
Tarea programada: revisa precios en dos tiendas online y avisa por Telegram
(con foto) de las rebajas nuevas, de lo que baja más de precio y de lo que pasa
a "últimas unidades". Guarda lo que ya vio en estado.json.

Solo usa la librería estándar de Python.

Variables de entorno:
  TELEGRAM_TOKEN     Clave de Telegram
  TELEGRAM_CHAT_ID   A quién avisar: número de chat, canal (@nombre) o grupo.
                     Varios separados por comas.
  (si faltan, no envía nada y solo imprime los mensajes: modo prueba)

  DESCUENTO_MINIMO   Solo avisar si el descuento es >= este % (por defecto 0)
  ULTIMAS_SIEMPRE    1 = avisar de todas las últimas unidades aunque no lleguen
                     a DESCUENTO_MINIMO (por defecto 1)
  PRECIO_MAXIMO      Precio máximo en la tienda A, en pesos (0 = sin límite)
  PRECIO_MAXIMO_EUR  Precio máximo en la tienda B, en euros (0 = sin límite)
  INCLUIR_ESPANA     1 = revisar también la tienda B (por defecto 1)
  PALABRAS_CLAVE     Lista separada por comas (vacío = todo)
  INCLUIR_FAMILY     1 = incluir precios de socios (por defecto 1)
  INCLUIR_ULTIMAS    1 = avisar de últimas unidades (por defecto 1)
  INCLUIR_DESTACADOS 1 = vigilar la lista de productos destacados de la tienda A (1)
  DESTACADOS_SIEMPRE 1 = avisar de lo que entra en esa lista aunque no llegue al mínimo (1)
  MAX_FOTOS          Productos con foto por revisión; el resto va en una lista (10)
  CAMA_Y_COLCHON     1 = vigilar aparte camas y colchones (por defecto 0)
  CAMA_TAMANOS       Tamaños a vigilar: twin, full, queen, king (ej. "full,queen")
  CAMA_DESCUENTO_MINIMO  Descuento mínimo para esa vigilancia (por defecto 1 = cualquiera)
"""

import base64
import hashlib
import html
import http.cookiejar
import json
import os
import re
import sys
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import uuid
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone

def _t(texto):
    return base64.b64decode(texto).decode()


MARCA = _t("SUtFQQ==")
BASE = _t("aHR0cHM6Ly93d3cuaWtlYS5jb20uZG8=")                    # tienda A
BASE_B = _t("aHR0cHM6Ly93d3cuaWtlYS5jb20=")                     # tienda B
FOTOS_A = _t("c3RhdGljMi5pa2VhLmNvbS5kbw==")
MONEDA_A = _t("UkQk")
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/130.0 Safari/537.36")
HORA_RD = timezone(timedelta(hours=-4))
ARCHIVO_ESTADO = os.path.join(os.path.dirname(os.path.abspath(__file__)), "estado.json")

PAUSA_ENTRE_PAGINAS = 0.3   # segundos, para no cargar la web
DIAS_OLVIDO = 3             # si un producto no aparece en 3 días, se olvida
MAX_CARACTERES_LISTA = 3800  # Telegram admite hasta 4096 por mensaje
MAX_MENSAJES_LISTA = 3
MAX_LINEAS_LISTA = 25        # productos por mensaje de lista


def env_num(nombre, defecto):
    try:
        return float(os.environ.get(nombre, "").strip() or defecto)
    except ValueError:
        return float(defecto)


DESCUENTO_MINIMO = env_num("DESCUENTO_MINIMO", 0)
ULTIMAS_SIEMPRE = env_num("ULTIMAS_SIEMPRE", 1) == 1
PRECIO_MAXIMO = env_num("PRECIO_MAXIMO", 0)
PRECIO_MAXIMO_EUR = env_num("PRECIO_MAXIMO_EUR", 0)
INCLUIR_ESPANA = env_num("INCLUIR_ESPANA", 1) == 1
INCLUIR_FAMILY = env_num("INCLUIR_FAMILY", 1) == 1
INCLUIR_ULTIMAS = env_num("INCLUIR_ULTIMAS", 1) == 1
INCLUIR_DESTACADOS = env_num("INCLUIR_DESTACADOS", 1) == 1
DESTACADOS_SIEMPRE = env_num("DESTACADOS_SIEMPRE", 1) == 1
MAX_FOTOS = int(env_num("MAX_FOTOS", 5))
RESUMEN_DIARIO = env_num("RESUMEN_DIARIO", 0) == 1
RESUMEN_HORA = int(env_num("RESUMEN_HORA", 21))   # hora local (RD) a partir de la que se manda
CAMA_Y_COLCHON = env_num("CAMA_Y_COLCHON", 0) == 1
CAMA_TAMANOS = {x.strip().lower() for x in os.environ.get("CAMA_TAMANOS", "full,queen").split(",") if x.strip()}
CAMA_DESCUENTO_MINIMO = env_num("CAMA_DESCUENTO_MINIMO", 1)

TELEGRAM_TOKEN = os.environ.get("TELEGRAM_TOKEN", "").strip()
TELEGRAM_CHATS = [c.strip() for c in os.environ.get("TELEGRAM_CHAT_ID", "").split(",") if c.strip()]


def sin_acentos(texto):
    texto = unicodedata.normalize("NFKD", texto.lower())
    return "".join(c for c in texto if not unicodedata.combining(c))


PALABRAS_CLAVE = [sin_acentos(p.strip())
                  for p in os.environ.get("PALABRAS_CLAVE", "").split(",") if p.strip()]

_SEC_A = json.loads(_t("eyJvZmVydGFzIjogIm9mZXJ0YXMiLCAiYmFqYWRhcyI6ICJoZW1vcy1iYWphZG8tcHJlY2lvIiwgImZhbWlseSI6ICJwcmVjaW9zLWlrZWEtZmFtaWx5IiwgInVsdGltYXMiOiAidWx0aW1hcy11bmlkYWRlcyJ9"))
SECCIONES = [_SEC_A["ofertas"], _SEC_A["bajadas"]]
if INCLUIR_FAMILY:
    SECCIONES.append(_SEC_A["family"])
if INCLUIR_ULTIMAS:
    SECCIONES.append(_SEC_A["ultimas"])
# Lista de productos destacados de la tienda A.
SLUG_DESTACADOS = _t("dW4tZ3Jhbi1wcm9kdWN0by1hLXVuLWJ1ZW4tcHJlY2lv")
NOMBRE_DESTACADOS = _t("VW4gZ3JhbiBwcm9kdWN0byBhIHVuIGJ1ZW4gcHJlY2lv")
if INCLUIR_DESTACADOS:
    SECCIONES.append(SLUG_DESTACADOS)

# Tienda B: su buscador interno (devuelve JSON).
ES_BUSCADOR = _t("aHR0cHM6Ly9zaWsuc2VhcmNoLmJsdWUuY2R0YXBwcy5jb20vZXMvZXMvc2VhcmNoP2M9bGlzdGFmJnY9MjAyNjA3Mjc=")
_SEC_B = json.loads(_t("eyJiYWphZGFzIjogIm5ld19sb3dlcl9wcmljZSIsICJ0aWVtcG8iOiAidGltZV9yZXN0cmljdGVkIiwgInRpZW5kYSI6ICI3MDA4MzQiLCAiZmFtaWx5IjogImZhbWlseV9wcmljZSIsICJ1bHRpbWFzIjogImxhc3RfY2hhbmNlIn0="))
SECCIONES_ES = [(_SEC_B["bajadas"], "SPECIAL"),    # bajadas de precio
                (_SEC_B["tiempo"], "SPECIAL"),     # ofertas por tiempo limitado
                (_SEC_B["tienda"], "CATEGORY")]    # ofertas solo en tienda física
# Más secciones con rebajas (incluyen productos que no salen en las anteriores).
SECCIONES_ES += [(x, "SPECIAL") for x in json.loads(_t("WyJyZWR1Y2VkX3ByaWNlIiwgImluX3N0b3JlX3ByaWNlX29ubHkiXQ=="))]
if INCLUIR_FAMILY:
    SECCIONES_ES.append((_SEC_B["family"], "SPECIAL"))
if INCLUIR_ULTIMAS:
    SECCIONES_ES.append((_SEC_B["ultimas"], "SPECIAL"))  # última oportunidad
if not INCLUIR_ESPANA:
    SECCIONES_ES = []


def etiqueta(que):
    """Nombre neutro de una sección para los registros (A1, A2… / B1, B2…)."""
    if que in SECCIONES:
        return f"A{SECCIONES.index(que) + 1}"
    nombres_b = [e for e, _ in SECCIONES_ES]
    clave = que[0] if isinstance(que, tuple) else que
    if clave in nombres_b:
        return f"B{nombres_b.index(clave) + 1}"
    return "?"


def log(*args):
    print(*args, file=sys.stderr, flush=True)


# --------------------------------------------------------------------------
# Descarga de la tienda A
# --------------------------------------------------------------------------

def nueva_sesion():
    # La web recuerda en la sesión (cookie) qué listado estás viendo, y el
    # botón "Cargar más" pide las páginas siguientes de ese listado.
    jar = http.cookiejar.CookieJar()
    return urllib.request.build_opener(urllib.request.HTTPCookieProcessor(jar))


def descargar(sesion, url, cabeceras=None, intentos=5):
    hdrs = {"User-Agent": UA, "Accept-Language": "es-DO,es;q=0.9"}
    hdrs.update(cabeceras or {})
    for i in range(intentos):
        try:
            req = urllib.request.Request(url, headers=hdrs)
            with sesion.open(req, timeout=30) as r:
                return r.read().decode("utf-8", "replace")
        except Exception as e:  # la web a veces corta la conexión: reintentar
            if i == intentos - 1:
                raise
            espera = 2 ** (i + 1)
            log(f"    fallo al descargar ({e}); reintento en {espera}s")
            time.sleep(espera)


_DECODER = json.JSONDecoder()


def extraer_productos(html):
    """Cada producto del listado trae sus datos en un `var item = {...}`."""
    productos = []
    for m in re.finditer(r"var item = ", html):
        try:
            obj, _ = _DECODER.raw_decode(html, m.end())
        except ValueError:
            continue
        if isinstance(obj, dict) and obj.get("partnumber"):
            productos.append(obj)
    return productos


def mostrando(html):
    m = re.search(r"Mostrando\s+(\d+)\s+de\s+(\d+)", html)
    return (int(m.group(1)), int(m.group(2))) if m else (None, None)


def atributo(etiqueta, nombre):
    m = re.search(rf'(?<![\w-]){nombre}="([^"]*)"', etiqueta)  # no confundir con data-name=
    return m.group(1) if m else None


def filtros_de_pagina(html):
    """Los mismos filtros que manda el botón "Cargar más" de la web."""
    params = []
    for etiqueta in re.findall(r"<input\b[^>]*>", html):
        nombre = atributo(etiqueta, "name")
        if not nombre:
            continue
        valor = atributo(etiqueta, "value") or ""
        es_switch = "filter-switch_js" in (atributo(etiqueta, "class") or "")
        if es_switch and re.search(r"\schecked\b", etiqueta):
            params.append((nombre, "1"))
        elif (atributo(etiqueta, "type") == "hidden"
              and (nombre in ("id_custom_page", "complete", "fg")
                   or nombre.startswith("hidden_is_"))):
            params.append((nombre, valor))
    params = list(dict.fromkeys(params))  # sin duplicados
    m = re.search(r'id="orderFilter"[^>]*data-value="([^"]*)"', html)
    orden = m.group(1) if m else ""
    return params, orden


def leer_seccion(slug):
    sesion = nueva_sesion()
    url = f"{BASE}/es/{slug}"
    html = descargar(sesion, url)
    productos = extraer_productos(html)
    vistos, total = mostrando(html)
    params, orden = filtros_de_pagina(html)

    # Las páginas hay que pedirlas en orden (la web recuerda por cuál vas).
    pagina = 2
    while total and vistos and vistos < total and pagina <= 200:
        time.sleep(PAUSA_ENTRE_PAGINAS)
        consulta = urllib.parse.urlencode(params + [("page", pagina), ("order", orden)])
        try:
            texto = descargar(
                sesion,
                f"{BASE}/es/products/template_reload?{consulta}",
                {"X-Requested-With": "XMLHttpRequest",
                 "Accept": "application/json, text/javascript, */*; q=0.01",
                 "Referer": url},
            )
            data = json.loads(texto)
        except Exception as e:
            log(f"  {etiqueta(slug)}: fallo en la página {pagina} ({e}); me quedo con lo leído")
            break
        nuevos = extraer_productos(data.get("result", ""))
        if not nuevos:
            break
        productos.extend(nuevos)
        nuevos_vistos, _ = mostrando(data.get("pagination_one_btn", ""))
        vistos = nuevos_vistos if nuevos_vistos else vistos + len(nuevos)
        pagina += 1

    log(f"  {etiqueta(slug)}: leídos {len(productos)} de {total or len(productos)}")
    if total and len(productos) < total * 0.9:
        log(f"  {etiqueta(slug)}: aviso: faltan productos (la web pudo fallar o cambiar)")
    return productos


def leer_espana(entrada, tipo):
    """Pide al buscador de la tienda B todos los productos de una sección."""
    productos, maximo = [], None
    while maximo is None or len(productos) < maximo:
        cuerpo = {"searchParameters": {"input": entrada, "type": tipo},
                  "components": [{"component": "PRIMARY_AREA",
                                  "types": {"main": "PRODUCT", "breakouts": []},
                                  "filterConfig": {},
                                  "window": {"size": 500, "offset": len(productos)}}]}
        for intento in range(4):
            try:
                req = urllib.request.Request(
                    ES_BUSCADOR, data=json.dumps(cuerpo).encode(),
                    headers={"Content-Type": "application/json", "User-Agent": UA,
                             "Origin": BASE_B, "Referer": BASE_B + "/es/es/"})
                with urllib.request.urlopen(req, timeout=30) as r:
                    data = json.loads(r.read().decode("utf-8"))
                break
            except Exception as e:
                if intento == 3:
                    raise
                log(f"    {etiqueta(entrada)}: fallo ({e}); reintento")
                time.sleep(2 ** (intento + 1))
        area = next((x for x in data.get("results", []) if x.get("component") == "PRIMARY_AREA"), {})
        nuevos = [i["product"] for i in area.get("items", []) if isinstance(i.get("product"), dict)]
        maximo = int((area.get("metadata") or {}).get("max") or 0)
        if not nuevos:
            break
        productos.extend(nuevos)
        if len(productos) > 5000:
            break
    log(f"  {etiqueta(entrada)}: leídos {len(productos)} de {maximo or len(productos)}")
    return productos


def leer_tarea(tarea):
    """Lee una sección de la tienda A o B sin que un fallo pare todo lo demás."""
    pais, que = tarea
    try:
        if pais == "do":
            return pais, que, leer_seccion(que)
        return pais, que, leer_espana(*que)
    except Exception as e:
        log(f"  {etiqueta(que)}: no se pudo leer ({e})")
        return pais, que, None


def leer_seccion_segura(slug):
    """Si una sección falla, las demás siguen; lo ya visto no se pierde."""
    try:
        return leer_seccion(slug)
    except Exception as e:
        log(f"  {etiqueta(slug)}: no se pudo leer ({e})")
        return None


# --------------------------------------------------------------------------
# Interpretar precios
# --------------------------------------------------------------------------

def num(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return 0.0


def ofertas_de(item, hoy, destacado=False):
    """Devuelve las rebajas que tiene un producto (puede tener más de una)."""
    actual = num(item.get("current_price"))
    original = num(item.get("original_price"))
    oferta = num(item.get("offer_price"))
    antes_hbp = num(item.get("hbp_price"))
    family = num(item.get("family_price"))
    ultimas = INCLUIR_ULTIMAS and bool(item.get("last_units"))
    foto = (item.get("default_image") or item.get("_original_default_image") or "").strip()
    if foto.startswith("/"):
        foto = BASE + foto

    base = {
        "pais": "do",
        "foto": solo_tienda(foto),
        "id": str(item["partnumber"]),
        "nombre": (item.get("name") or "").strip(),
        "detalle": ", ".join(x for x in [(item.get("facts") or "").strip(),
                                         (item.get("valid_design") or "").strip()] if x),
        "url": BASE + (item.get("url") or ""),
        "stock": item.get("stock"),
        "ultimas": ultimas,
        "destacado": destacado,
        "tipo_producto": (item.get("facts") or "").strip(),
        "medidas": " ".join(str(x) for x in (item.get("size"), item.get("resume_measure_metric"),
                                             item.get("alternative_metric")) if x),
    }
    resultado = []

    if oferta > 0 and original > oferta:
        resultado.append({**base, "tipo": "oferta", "ahora": oferta, "antes": original})
    elif antes_hbp > actual > 0:
        resultado.append({**base, "tipo": "bajada", "ahora": actual, "antes": antes_hbp})

    if INCLUIR_FAMILY and family > 0 and actual > family:
        ini, fin = item.get("family_price_fi") or "", item.get("family_price_ff") or ""
        # Algunos precios Family vienen sin fechas: se dan por vigentes (salen en la web).
        if (not ini or ini <= hoy) and (not fin or hoy <= fin):
            precio_normal = oferta if 0 < oferta < actual else actual
            if family < precio_normal:
                resultado.append({**base, "tipo": "family", "ahora": family,
                                  "antes": precio_normal, "hasta": fin})

    # Últimas unidades sin rebaja: también interesa saberlo.
    if not resultado and (ultimas or destacado) and actual > 0:
        resultado.append({**base, "tipo": "ultimas" if ultimas else "destacado",
                          "ahora": actual, "antes": actual})

    for r in resultado:
        r["descuento"] = round((1 - r["ahora"] / r["antes"]) * 100)
    return resultado


def precio_api(d):
    """Convierte {"wholeNumber": "12", "decimals": "99"} en 12.99."""
    if not isinstance(d, dict):
        return 0.0
    entero = re.sub(r"\D", "", d.get("wholeNumber") or "") or "0"
    decimales = re.sub(r"\D", "", d.get("decimals") or "") or "0"
    return float(f"{entero}.{decimales}")


def numero_euros(texto):
    """'149€' -> 149.0, '39.99€' -> 39.99, '1.299€' -> 1299.0, '10,99 €' -> 10.99"""
    m = re.search(r"(\d[\d.,]*)\s*€", texto or "")
    if not m:
        return 0.0
    t = m.group(1).rstrip(".,")
    if "," in t:
        t = t.replace(".", "").replace(",", ".")
    elif re.search(r"\.\d{3}$", t):
        t = t.replace(".", "")
    try:
        return float(t)
    except ValueError:
        return 0.0


def solo_tienda(url, por_defecto=""):
    """Por seguridad, solo se aceptan enlaces y fotos de las webs de las tiendas."""
    host = urllib.parse.urlparse(url or "").hostname or ""
    permitidos = {urllib.parse.urlparse(BASE).hostname, urllib.parse.urlparse(BASE_B).hostname, FOTOS_A}
    if (url or "").startswith("https://") and host in permitidos:
        return url
    return por_defecto


def ofertas_es(p):
    """Rebajas de un producto de la tienda B (mismo formato que ofertas_de)."""
    precio = p.get("salesPrice") or {}
    actual = num(precio.get("numeral"))
    anterior = precio_api(precio.get("previous"))
    texto_anuncio = (precio.get("advertisement") or {}).get("text") or ""
    if not anterior and "anterior" in texto_anuncio.lower():
        # Algunos productos traen el precio anterior solo en el texto: "Precio anterior 19,99€"
        anterior = numero_euros(texto_anuncio)
    etiquetas = set(precio.get("tags") or []) | {p.get("tag")}
    ultimas = INCLUIR_ULTIMAS and bool(p.get("lastChance"))
    base = {
        "pais": "es",
        "foto": solo_tienda(p.get("mainImageUrl")),
        "id": str(p.get("id") or p.get("itemNo") or ""),
        "nombre": (p.get("name") or "").strip(),
        "detalle": ", ".join(x for x in [p.get("typeName"), p.get("validDesignText"),
                                         p.get("itemMeasureReferenceText")] if x),
        "url": solo_tienda(p.get("pipUrl"), BASE_B + "/es/es/offers/"),
        "stock": None,
        "ultimas": ultimas,
        "destacado": False,
        "tipo_producto": (p.get("typeName") or "").strip(),
        "medidas": p.get("itemMeasureReferenceText") or "",
    }
    resultado = []

    if anterior > actual > 0:
        if "FAMILY_PRICE" in etiquetas:
            if INCLUIR_FAMILY:
                resultado.append({**base, "tipo": "family", "ahora": actual, "antes": anterior,
                                  "hasta": precio.get("validTo") or ""})
        else:
            tipo = "bajada" if "NEW_LOWER_PRICE" in etiquetas else "oferta"
            resultado.append({**base, "tipo": tipo, "ahora": actual, "antes": anterior})

    anuncio = precio.get("advertisement") or {}
    texto_tienda = (anuncio.get("text") or "").lower()
    if (("LOWER_CURRENT_REGULAR_PRICE_IN_STORE" in etiquetas or "solo en tienda" in texto_tienda)
            and actual > 0 and "anterior" not in texto_tienda):
        en_tienda = numero_euros(anuncio.get("text"))
        if not en_tienda and precio.get("lowerInStorePricePercentage"):
            en_tienda = round(actual * (1 - num(precio["lowerInStorePricePercentage"]) / 100), 2)
        if 0 < en_tienda < actual:
            resultado.append({**base, "tipo": "tienda", "ahora": en_tienda, "antes": actual,
                              "hasta": anuncio.get("validTo") or ""})

    if not resultado and ultimas and actual > 0:
        resultado.append({**base, "tipo": "ultimas", "ahora": actual, "antes": actual})

    for r in resultado:
        r["descuento"] = round((1 - r["ahora"] / r["antes"]) * 100)
    return resultado


def clave_de(o):
    return f'{"es-" if o["pais"] == "es" else ""}{o["tipo"]}:{o["id"]}'


def pais_de_clave(clave):
    return "es" if clave.startswith("es-") else "do"


NOMBRE_TAMANO = {"twin": "Individual", "full": "Full/Doble", "queen": "Queen", "king": "King"}


def cama_o_colchon(o):
    """'colchon', 'cama' o None, según el tipo de producto."""
    tipo = sin_acentos(o.get("tipo_producto") or "").strip()
    if tipo.startswith("colchon"):
        return "colchon"
    excluir = ("sofa", "litera", "camarote", "cuna", "nino", "infantil", "de dia", "nido", "alta",
               "tienda", "bandeja", "funda", "ropa", "manta", "colcha", "patas")
    if (tipo.startswith(("estructura de cama", "estructura cama", "cama", "base de cama", "base cama",
                         "muebles de dormitorio"))
            and not any(x in tipo for x in excluir)):
        return "cama"
    return None


def tamano_cama(o):
    """twin / full / queen / king, por la palabra o por el ancho en cm."""
    texto = sin_acentos(" ".join([o.get("tipo_producto") or "", o.get("detalle") or "", o.get("medidas") or ""]))
    for palabra, tam in (("king", "king"), ("queen", "queen"), ("full", "full"), ("matrimonial", "full"),
                         ("twin", "twin"), ("individual", "twin")):
        if re.search(rf"\b{palabra}\b", texto):
            return tam
    m = re.search(r"(\d{2,3})(?:[.,]\d+)?\s*x\s*\d", sin_acentos(o.get("medidas") or ""))
    if m:
        ancho = int(m.group(1))
        if 85 <= ancho < 130:
            return "twin"
        if 130 <= ancho < 150:
            return "full"
        if 150 <= ancho <= 170:
            return "queen"
        if ancho > 170:
            return "king"
    return None


def para_mi_cama(o):
    return (CAMA_Y_COLCHON and cama_o_colchon(o) is not None and tamano_cama(o) in CAMA_TAMANOS
            and o["descuento"] >= CAMA_DESCUENTO_MINIMO and (o["stock"] is None or num(o["stock"]) > 0))


def pasa_filtros(o):
    if o["stock"] is not None and num(o["stock"]) <= 0:
        return False
    # Las últimas unidades se avisan siempre (si así está configurado), porque se acaban.
    excepcion = (ULTIMAS_SIEMPRE and o["ultimas"]) or (DESTACADOS_SIEMPRE and o.get("destacado_aviso"))
    if o["descuento"] < DESCUENTO_MINIMO and not excepcion:
        return False
    limite = PRECIO_MAXIMO_EUR if o["pais"] == "es" else PRECIO_MAXIMO
    if limite and o["ahora"] > limite:
        return False
    if PALABRAS_CLAVE:
        texto = sin_acentos(f'{o["nombre"]} {o["detalle"]}')
        if not any(p in texto for p in PALABRAS_CLAVE):
            return False
    return True


# --------------------------------------------------------------------------
# Mensajes de Telegram
# --------------------------------------------------------------------------

def rd(valor):
    return MONEDA_A + f"{valor:,.0f}"


def euros(valor):
    texto = f"{valor:,.2f}".replace(",", " ").replace(".", ",").replace(" ", ".")
    return (texto[:-3] if texto.endswith(",00") else texto) + " €"


def dinero(valor, pais):
    return euros(valor) if pais == "es" else rd(valor)


TIENDA = {"do": f"🇩🇴 {MARCA} RD", "es": f"🇪🇸 {MARCA} España"}


def esc(texto):
    return html.escape(texto or "", quote=False)


ETIQUETA = {"oferta": "🏷️ Oferta", "bajada": "📉 Bajó de precio",
            "family": f"💳 {MARCA} Family", "ultimas": "⚠️ Últimas unidades",
            "tienda": "🏬 Solo en tienda", "destacado": "⭐ " + NOMBRE_DESTACADOS}


def precio_html(o):
    p = o["pais"]
    if o["descuento"] > 0:
        return f'<s>{dinero(o["antes"], p)}</s> → <b>{dinero(o["ahora"], p)}</b> (-{o["descuento"]}%)'
    return f'<b>{dinero(o["ahora"], p)}</b>'


def ficha(o):
    """Texto que acompaña a la foto de un producto."""
    etiqueta = ETIQUETA[o["tipo"]]
    if o["pais"] == "es" and o["tipo"] == "ultimas":
        etiqueta = "⚠️ Última oportunidad"
    lineas = [
        f'{TIENDA[o["pais"]]} · {etiqueta}',
        f'<a href="{esc(o["url"])}"><b>{esc(o["nombre"])}</b></a> {esc(o["detalle"])}'.strip(),
        precio_html(o),
    ]
    ultimas = "¡Última oportunidad!" if o["pais"] == "es" else "¡Últimas unidades!"
    if o.get("entro_ultimas"):
        lineas.append("⚠️ ¡Ahora es última oportunidad!" if o["pais"] == "es"
                      else "⚠️ ¡Ahora quedan las últimas unidades!")
    elif o["ultimas"] and o["tipo"] != "ultimas":
        lineas.append(f"⚠️ {ultimas}")
    if o.get("entro_destacado"):
        lineas.append(f"⭐ ¡Nuevo en «{NOMBRE_DESTACADOS}»!")
    elif o.get("destacado") and o["tipo"] != "destacado":
        lineas.append(f"⭐ {NOMBRE_DESTACADOS}")
    if o.get("precio_previo"):
        lineas.append(f'📉 ¡Bajó otra vez! La última vez estaba a {dinero(o["precio_previo"], o["pais"])}')
    hasta = (f', hasta el {o["hasta"][8:10]}/{o["hasta"][5:7]}'
             if re.match(r"\d{4}-\d{2}-\d{2}", o.get("hasta") or "") else "")
    if o["tipo"] == "family":
        lineas.append(f"Solo socios {MARCA} Family{hasta}")
    if o["tipo"] == "tienda":
        lineas.append(f"Precio solo en tiendas físicas de España{hasta}")
    return "\n".join(lineas)


def linea_corta(o):
    """Una línea por producto, para la lista del final."""
    icono = (ETIQUETA[o["tipo"]].split()[0]
             + (" ⚠️" if o["ultimas"] and o["tipo"] != "ultimas" else "")
             + (" ⭐" if o.get("destacado") and o["tipo"] != "destacado" else ""))
    detalle = o["detalle"] if len(o["detalle"]) <= 45 else o["detalle"][:44].rstrip(" ,") + "…"
    return (f'{icono} <a href="{esc(o["url"])}"><b>{esc(o["nombre"])}</b></a> '
            f'{esc(detalle)}: {precio_html(o)}')


def visible(texto):
    """Lo que cuenta Telegram para el límite de 4096: el texto sin las etiquetas ni enlaces."""
    return len(html.unescape(re.sub(r"<[^>]+>", "", texto)))


def tramo(o, minimo=None):
    """Tramo de 5% del descuento (45, 50, 55…); -1 para lo que entra por otra regla."""
    minimo = DESCUENTO_MINIMO if minimo is None else minimo
    if o["descuento"] >= minimo and o["descuento"] > 0:
        return int(o["descuento"] // 5 * 5)
    return -1


def titulo_tramo(t, pais):
    tienda = TIENDA[pais]
    if t < 0:
        nombre = "⚠️ <b>Última oportunidad</b>" if pais == "es" else "⚠️⭐ <b>Últimas unidades y destacados</b>"
        return f"{tienda} · {nombre}"
    icono = "🔥" if t >= 70 else "💥" if t >= 50 else "🏷️"
    return f"{tienda} · {icono} <b>{t}–{min(t + 4, 100)}% de descuento</b>"


def armar_listas(ofertas, max_mensajes=MAX_MENSAJES_LISTA, minimo=None):
    """Lista sin fotos: primero por país (RD, España) y dentro por tramos de 5% de descuento."""
    grupos = {}
    for o in ofertas:
        grupos.setdefault((o["pais"], tramo(o, minimo)), []).append(o)
    orden = sorted(grupos, key=lambda g: (("do", "es").index(g[0]), -g[1]))
    mensajes, actual, lineas, incluidos, lleno = [], "", 0, 0, False
    for pais, t in orden:
        cabecera, primera = titulo_tramo(t, pais), True
        for o in sorted(grupos[(pais, t)], key=lambda o: (-o["descuento"], o["ahora"])):
            linea = linea_corta(o)
            if actual and (visible(actual) + visible(linea) + 80 > MAX_CARACTERES_LISTA
                           or lineas >= MAX_LINEAS_LISTA):
                mensajes.append(actual)
                actual, lineas = "", 0
                if len(mensajes) >= max_mensajes:
                    lleno = True
                    break
            if not actual:
                actual = cabecera + ("" if primera else " <i>(sigue)</i>")
            elif primera:
                actual += "\n\n" + cabecera
            actual += "\n" + linea
            primera, lineas, incluidos = False, lineas + 1, incluidos + 1
        if lleno:
            break
    if actual and not lleno:
        mensajes.append(actual)
    restantes = len(ofertas) - incluidos
    if restantes > 0 and mensajes:
        web = BASE + "/es/ofertas" if ofertas[0]["pais"] == "do" else BASE_B + "/es/es/offers/"
        mensajes[-1] += f'\n\n…y {restantes} más en <a href="{web}">la web</a>'
    return mensajes


class ErrorTelegram(Exception):
    def __init__(self, codigo, descripcion):
        super().__init__(f"Telegram {codigo}: {descripcion}")
        self.codigo = codigo


def multipart(campos, foto_bytes):
    limite = "limite" + uuid.uuid4().hex
    partes = [f'--{limite}\r\nContent-Disposition: form-data; name="{k}"\r\n\r\n{v}\r\n'.encode()
              for k, v in campos.items()]
    partes.append((f'--{limite}\r\nContent-Disposition: form-data; name="photo"; '
                   f'filename="foto.jpg"\r\nContent-Type: image/jpeg\r\n\r\n').encode()
                  + foto_bytes + b"\r\n")
    partes.append(f"--{limite}--\r\n".encode())
    return b"".join(partes), f"multipart/form-data; boundary={limite}"


def telegram(metodo, datos, foto_bytes=None):
    url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/{metodo}"
    for intento in range(5):
        if foto_bytes is None:
            cuerpo, tipo = json.dumps(datos).encode(), "application/json"
        else:
            campos = {k: (json.dumps(v) if isinstance(v, (dict, list)) else str(v))
                      for k, v in datos.items()}
            cuerpo, tipo = multipart(campos, foto_bytes)
        req = urllib.request.Request(url, data=cuerpo, headers={"Content-Type": tipo})
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                respuesta = json.loads(r.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            try:
                respuesta = json.loads(e.read().decode("utf-8"))
            except ValueError:
                respuesta = {"ok": False, "error_code": e.code, "description": e.reason}
        except (urllib.error.URLError, TimeoutError, ConnectionError) as e:
            if intento == 4:
                raise
            log(f"    Telegram no responde ({e}); reintento")
            time.sleep(2 ** (intento + 1))
            continue

        if respuesta.get("ok"):
            # Telegram permite ~1 mensaje por segundo a un chat (20/min a un grupo o canal).
            time.sleep(3.1 if str(datos.get("chat_id", "")).startswith(("-", "@")) else 1.1)
            return respuesta.get("result")
        espera = (respuesta.get("parameters") or {}).get("retry_after")
        if respuesta.get("error_code") == 429 and espera:
            log(f"    Telegram pide esperar {espera} s")
            time.sleep(int(espera) + 1)
            continue
        raise ErrorTelegram(respuesta.get("error_code"), respuesta.get("description"))
    raise ErrorTelegram(None, "demasiados reintentos")


def descargar_bytes(url):
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=60) as r:
        return r.read()


def enviar_texto(chat, texto, boton=None, tarjeta=None):
    # tarjeta = enlace del que Telegram saca la vista previa (foto pequeña, título y descripción)
    vista = ({"url": tarjeta, "prefer_small_media": True, "show_above_text": False}
             if tarjeta else {"is_disabled": True})
    datos = {"chat_id": chat, "text": texto, "parse_mode": "HTML", "link_preview_options": vista}
    if boton:
        datos["reply_markup"] = boton
    telegram("sendMessage", datos)


def enviar_producto(chat, o):
    """El producto con su precio y, debajo, la tarjeta pequeña con la foto (vista previa del enlace)."""
    boton = {"inline_keyboard": [[{"text": f"Ver en {MARCA}", "url": o["url"]}]]}
    texto = ficha(o)
    try:
        return enviar_texto(chat, texto, boton, tarjeta=o["url"])
    except ErrorTelegram as e:
        if e.codigo != 400:
            raise
        log(f"    Telegram no aceptó una tarjeta ({e}); mando solo el texto")
    return enviar_texto(chat, texto, boton)


def notificar(encabezado, ofertas, chats=None, fotos=None, max_listas=MAX_MENSAJES_LISTA, minimo=None):
    """Encabezado y, por cada país: los de más descuento con tarjeta y el resto en lista por tramos."""
    chats = TELEGRAM_CHATS if chats is None else chats
    fotos = MAX_FOTOS if fotos is None else fotos
    paises = [p for p in ("do", "es") if any(o["pais"] == p for o in ofertas)]
    partes = [("texto", encabezado)]   # en orden: ("texto", html) o ("producto", oferta)
    for pais in paises:
        del_pais = [o for o in ofertas if o["pais"] == pais]
        con_foto = sorted(del_pais, key=lambda o: (-o["descuento"], o["ahora"]))[:fotos]
        elegidos = {id(o) for o in con_foto}
        resto = [o for o in del_pais if id(o) not in elegidos]
        if len(paises) > 1 and con_foto:
            partes.append(("texto", f"<b>{TIENDA[pais]}</b> · {len(del_pais)} "
                                    f"{'producto' if len(del_pais) == 1 else 'productos'}"))
        partes += [("producto", o) for o in con_foto]
        listas = armar_listas(resto, max_listas, minimo)
        if resto and listas and con_foto:
            listas[0] = f"<b>Y {len(resto)} más de {TIENDA[pais]}:</b>\n\n" + listas[0]
        partes += [("texto", l) for l in listas]

    if not (TELEGRAM_TOKEN and TELEGRAM_CHATS):
        print("----- (modo prueba: no hay TELEGRAM_TOKEN/TELEGRAM_CHAT_ID) -----")
        for tipo, cosa in partes:
            if tipo == "producto":
                print(f'{ficha(cosa)}\n[tarjeta con foto pequeña: {cosa["url"]}]\n[botón Ver: {cosa["url"]}]\n')
            else:
                print(cosa, end="\n\n")
        return

    for chat in chats:
        for tipo, cosa in partes:
            if tipo == "producto":
                enviar_producto(chat, cosa)
            else:
                enviar_texto(chat, cosa)
        log(f"    Telegram: {len(partes)} mensajes enviados al chat {chat}")


# --------------------------------------------------------------------------
# Programa principal
# --------------------------------------------------------------------------

def buscar_canal_por_nombre(nombre):
    """Busca, entre los canales donde somos administradores, uno con ese nombre.

    Los canales privados no tienen dirección @, pero Telegram nos cuenta a
    qué canales lo añadieron y qué se publica en ellos (lo guarda 24 horas).
    """
    try:
        novedades = telegram("getUpdates", {"timeout": 0}) or []
    except ErrorTelegram as e:
        log(f"    no pude consultar los canales ({e})")
        return None
    buscado = sin_acentos(nombre).strip()
    encontrados = {}
    for u in novedades:
        for campo in ("my_chat_member", "channel_post", "edited_channel_post"):
            chat = (u.get(campo) or {}).get("chat") or {}
            if chat.get("type") == "channel" and sin_acentos(chat.get("title") or "").strip() == buscado:
                encontrados[str(chat["id"])] = chat.get("title")
    if len(encontrados) == 1:
        return next(iter(encontrados))
    if len(encontrados) > 1:
        log(f"    hay varios canales llamados «{nombre}»: pon su número en TELEGRAM_CHAT_ID")
    return None


SAL = _t("aWtlYS1ib3Q6")  # no cambiar: identifica los chats ya saludados


def revisiones_de_hoy(desde_utc):
    """(revisiones, fallos) de hoy según GitHub. None si no se puede saber."""
    token, repo = os.environ.get("GITHUB_TOKEN", ""), os.environ.get("GITHUB_REPOSITORY", "")
    if not (token and repo):
        return None
    url = (f"https://api.github.com/repos/{repo}/actions/runs?per_page=100&"
           f"created=%3E%3D{desde_utc}")
    try:
        req = urllib.request.Request(url, headers={"Authorization": f"Bearer {token}",
                                                   "Accept": "application/vnd.github+json", "User-Agent": UA})
        with urllib.request.urlopen(req, timeout=30) as r:
            corridas = json.loads(r.read().decode("utf-8")).get("workflow_runs", [])
    except Exception as e:
        log(f"    no pude contar las revisiones de hoy ({e})")
        return None
    terminadas = [c for c in corridas if c.get("status") == "completed"]
    fallos = sum(1 for c in terminadas if c.get("conclusion") == "failure")
    return len(terminadas) + 1, fallos   # +1: esta misma revisión


def huella(chat):
    """Identifica un chat en estado.json sin guardar su número tal cual."""
    return hashlib.sha256(f"{SAL}{chat}".encode()).hexdigest()[:16]


def main():
    if os.environ.get("GITHUB_ACTIONS") == "true" and not (TELEGRAM_TOKEN and TELEGRAM_CHATS):
        # En GitHub sin los secretos no tiene sentido revisar: se gastarían minutos
        # y el mensaje de activación se perdería sin que te llegue.
        print("::warning::Faltan los secretos TELEGRAM_TOKEN y/o TELEGRAM_CHAT_ID "
              "(Settings → Secrets and variables → Actions). No reviso nada todavía.")
        return

    ahora_rd = datetime.now(HORA_RD)
    hoy = ahora_rd.strftime("%Y-%m-%d")

    estado = None
    if os.path.exists(ARCHIVO_ESTADO):
        with open(ARCHIVO_ESTADO, encoding="utf-8") as f:
            estado = json.load(f)
    # Canales privados escritos por su nombre (@nombre) -> su número real de Telegram.
    canales = dict((estado or {}).get("canales", {}))

    # Comprobar Telegram antes de leer las tiendas (tarda varios minutos): si el
    # token o el número de chat están mal, mejor saberlo en segundos.
    # Si hay varias personas y el número de una está mal, se avisa igual a las demás.
    if TELEGRAM_TOKEN:
        validos = []
        for chat in TELEGRAM_CHATS:
            real = canales.get(chat.lower(), chat)
            try:
                telegram("getChat", {"chat_id": real})
                validos.append(real)
                continue
            except ErrorTelegram as e:
                error = e
            if chat.startswith("@"):
                encontrado = buscar_canal_por_nombre(chat[1:])
                if encontrado:
                    log(f"Canal «{chat[1:]}» encontrado: número {encontrado}. Lo recuerdo para la próxima vez.")
                    canales[chat.lower()] = encontrado
                    validos.append(encontrado)
                    continue
            print(f"::warning::Telegram rechaza el chat {chat}: {error}. Si es una persona, tiene que "
                  "pulsar Iniciar en el bot; si es un canal, el bot tiene que ser administrador.")
        if not validos:
            print("::error::Ningún chat de TELEGRAM_CHAT_ID funciona: revisa el secreto.")
            sys.exit(1)
        TELEGRAM_CHATS[:] = list(dict.fromkeys(validos))

    conocidos = (estado or {}).get("productos", {})
    # Chats (personas o canales) que ya recibieron la bienvenida. Con la versión
    # anterior no se guardaba: se dan por saludados los chats personales que ya había.
    if estado is not None and "chats_saludados" not in estado:
        saludados = {huella(c) for c in TELEGRAM_CHATS if not c.startswith(("@", "-"))}
    else:
        saludados = set((estado or {}).get("chats_saludados", []))
    # Cada país tiene su propio "primera vez": al añadir España no se te
    # mandan de golpe todas sus ofertas actuales, solo un resumen.
    paises_conocidos = {pais_de_clave(k) for k in conocidos}
    # Secciones con su propio "primera vez" (para no avisar de golpe de todo lo que ya había).
    secciones_activadas = set((estado or {}).get("secciones_activadas", []))
    destacados_activos = "destacados" in secciones_activadas

    tareas = [("do", slug) for slug in SECCIONES] + [("es", sec) for sec in SECCIONES_ES]
    log("Leyendo tienda A" + (" y tienda B…" if SECCIONES_ES else "…"))
    inicio = time.time()
    # Todas las secciones se leen a la vez para que la revisión tarde menos.
    with ThreadPoolExecutor(max_workers=len(tareas)) as hilos:
        leidos = list(hilos.map(leer_tarea, tareas))
    log(f"Lectura terminada en {time.time() - inicio:.0f} s")

    if all(items is None for _, _, items in leidos):
        log("No se pudo leer ninguna sección. No guardo nada.")
        sys.exit(1)

    actuales = {}
    for pais, que, items in leidos:
        destacado = pais == "do" and que == SLUG_DESTACADOS
        for item in items or []:
            for o in (ofertas_de(item, hoy, destacado) if pais == "do" else ofertas_es(item)):
                clave = clave_de(o)
                if clave in actuales:  # el mismo producto en varias secciones: juntar marcas
                    o["ultimas"] = o["ultimas"] or actuales[clave]["ultimas"]
                    o["destacado"] = o["destacado"] or actuales[clave]["destacado"]
                actuales[clave] = o
    for o in actuales.values():
        # La excepción al descuento mínimo solo vale cuando la lista ya estaba activada.
        o["destacado_aviso"] = o["destacado"] and destacados_activos

    if not actuales:
        log("No se encontró ninguna oferta: puede que la web haya cambiado. No guardo nada.")
        sys.exit(1)

    novedades = []
    for clave, o in actuales.items():
        if o["pais"] not in paises_conocidos:
            continue  # primera vez de este país: solo se manda el resumen de activación
        previo = conocidos.get(clave)
        if previo is None:
            novedades.append(o)
            continue
        bajo_mas = o["ahora"] < previo["precio"] - 0.005
        entro_ultimas = o["ultimas"] and not previo.get("ultimas")
        entro_destacado = o["destacado_aviso"] and not previo.get("destacado")
        if bajo_mas:
            o["precio_previo"] = previo["precio"]
        if entro_ultimas:
            o["entro_ultimas"] = True
        if entro_destacado:
            o["entro_destacado"] = True
        if bajo_mas or entro_ultimas or entro_destacado:
            novedades.append(o)

    # Primero las últimas unidades (se acaban), luego por % de descuento.
    avisar = sorted((o for o in novedades if pasa_filtros(o)),
                    key=lambda o: (not o["ultimas"], -o["descuento"], o["ahora"]))
    for pais in ("do", "es"):
        total = sum(1 for o in actuales.values() if o["pais"] == pais)
        if total:
            log(f"Tienda {'A' if pais == 'do' else 'B'}: {total} ofertas en total, "
                f"{sum(1 for o in novedades if o['pais'] == pais)} novedades, "
                f"{sum(1 for o in avisar if o['pais'] == pais)} pasan tus filtros")

    fecha = ahora_rd.strftime("%d/%m/%Y %I:%M %p").lower()
    for pais in ("do", "es"):
        del_pais = [o for o in actuales.values() if o["pais"] == pais]
        if pais in paises_conocidos or not del_pais:
            continue
        mejores = sorted((o for o in del_pais if pasa_filtros(o)),
                         key=lambda o: (-o["descuento"], o["ahora"]))
        n_ultimas = sum(1 for o in del_pais if o["ultimas"])
        nombre_ultimas = "última oportunidad" if pais == "es" else "últimas unidades"
        titulo = (f"Avisos de {MARCA} RD activados" if pais == "do"
                  else f"Ahora también vigilo {MARCA} España")
        encabezado = (f"✅ <b>{titulo}</b> ({fecha})\n"
                      f"Vigilando {len(del_pais)} ofertas de {TIENDA[pais]}"
                      + (f" ({n_ultimas} de {nombre_ultimas})" if INCLUIR_ULTIMAS else "")
                      + ". Te escribiré cuando salgan nuevas, cuando algo baje más de precio"
                      + (f" o cuando algo pase a {nombre_ultimas}" if INCLUIR_ULTIMAS else "")
                      + ".\n\nLas mayores rebajas de hoy:")
        notificar(encabezado, mejores[:min(MAX_FOTOS, 5)])

    # Primera vez de la lista de destacados: un resumen en vez de un aviso por producto.
    if INCLUIR_DESTACADOS and not destacados_activos and "do" in paises_conocidos:
        lista = sorted((o for o in actuales.values() if o["destacado"]),
                       key=lambda o: (-o["descuento"], o["ahora"]))
        if lista:
            notificar(f"⭐ <b>Ahora también vigilo «{NOMBRE_DESTACADOS}» de {TIENDA['do']}</b> ({fecha})\n"
                      f"Hay {len({o['id'] for o in lista})} productos en esa lista. Te avisaré cuando "
                      "añadan productos nuevos"
                      + (", tengan el descuento que tengan" if DESTACADOS_SIEMPRE else "")
                      + ".\n\nLos de más descuento, con foto, y debajo la lista completa:", lista, max_listas=10)
    # Resumen de las rebajas que ya existían y nunca se avisaron (se tomaron como "ya vistas").
    # - La primera vez: todas las que llegan al mínimo.
    # - Si después se baja el mínimo (ej. de 50% a 45%): solo las del tramo nuevo (45-49%).
    resumen_desde = (estado or {}).get("resumen_desde")
    if resumen_desde is None and "resumen_inicial" in secciones_activadas:
        resumen_desde = 50  # el primer resumen se hizo con el mínimo del 50%
    if DESCUENTO_MINIMO > 0 and paises_conocidos and (resumen_desde is None or DESCUENTO_MINIMO < resumen_desde):
        tope = resumen_desde if resumen_desde is not None else 1000
        todas = sorted((o for o in actuales.values()
                        if pasa_filtros(o) and DESCUENTO_MINIMO <= o["descuento"] < tope),
                       key=lambda o: (-o["descuento"], o["ahora"]))
        if todas:
            por_pais = " · ".join(f"{TIENDA[p].split()[0]} {sum(1 for o in todas if o['pais'] == p)}"
                                  for p in ("do", "es") if any(o["pais"] == p for o in todas))
            tramo = (f"del {DESCUENTO_MINIMO:.0f}% o más" if tope == 1000
                     else f"entre {DESCUENTO_MINIMO:.0f}% y {tope - 1:.0f}%")
            notificar(f"📋 <b>Todas las rebajas actuales {tramo}</b> ({fecha})\n"
                      f"{len(todas)} productos ({por_pais}). Son las que ya había y no te había mandado; "
                      "a partir de ahora solo te llegarán las nuevas.", todas, max_listas=20)
    if DESCUENTO_MINIMO > 0 and paises_conocidos:
        resumen_desde = DESCUENTO_MINIMO
        secciones_activadas.add("resumen_inicial")

    # Vigilancia aparte de camas y colchones. La primera vez, lo que hay ahora en oferta.
    tamanos = " y ".join(NOMBRE_TAMANO.get(x, x) for x in ("twin", "full", "queen", "king") if x in CAMA_TAMANOS)
    if CAMA_Y_COLCHON and "cama_resumen" not in secciones_activadas and paises_conocidos:
        camas = sorted((o for o in actuales.values() if para_mi_cama(o)), key=lambda o: (-o["descuento"], o["ahora"]))
        cuantos = " · ".join(f"{TIENDA[p].split()[0]} {sum(1 for o in camas if o['pais'] == p)}" for p in ("do", "es"))
        notificar(f"🛏️ <b>Camas y colchones {tamanos} en oferta ahora</b> ({fecha})\n"
                  f"{len(camas)} productos ({cuantos}). A partir de ahora te aviso de cada rebaja nueva "
                  "de camas y colchones de esos tamaños, aunque sea pequeña.", camas,
                  max_listas=10, minimo=CAMA_DESCUENTO_MINIMO)
        secciones_activadas.add("cama_resumen")

    # Una sola vez: la lista completa de destacados, sin fotos (las 5 primeras ya llegaron con foto).
    if (INCLUIR_DESTACADOS and "destacados" in secciones_activadas
            and "destacados_lista" not in secciones_activadas):
        lista = sorted((o for o in actuales.values() if o["destacado"]),
                       key=lambda o: (-o["descuento"], o["ahora"]))
        if lista:
            notificar(f"📋 <b>Lista completa de «{NOMBRE_DESTACADOS}»</b> ({fecha})\n"
                      f"{len(lista)} productos, de más a menos descuento:", lista, fotos=0, max_listas=10)
            secciones_activadas.add("destacados_lista")
    if INCLUIR_DESTACADOS and any(o["destacado"] for o in actuales.values()):
        if "destacados" not in secciones_activadas:
            secciones_activadas.add("destacados_lista")  # la activación ya incluye el resumen
        secciones_activadas.add("destacados")

    # Mensaje de comprobación, una sola vez (para confirmar que llegan los avisos desde aquí).
    if "comprobacion_envio" not in secciones_activadas and TELEGRAM_TOKEN and TELEGRAM_CHATS:
        n_a = sum(1 for o in actuales.values() if o["pais"] == "do")
        n_b = sum(1 for o in actuales.values() if o["pais"] == "es")
        for chat in TELEGRAM_CHATS:
            enviar_texto(chat, f"✅ <b>Comprobación</b> ({fecha})\nTodo funciona: acabo de revisar "
                               f"{n_a} ofertas de {TIENDA['do']} y {n_b} de {TIENDA['es']}. "
                               "Seguirás recibiendo aquí las rebajas nuevas, como hasta ahora.")
        secciones_activadas.add("comprobacion_envio")

    # Bienvenida a cada chat o canal nuevo, para que no se quede vacío hasta la próxima rebaja.
    # (Si es la primera vez, ya recibió arriba el mensaje de activación.)
    nuevos_chats = [c for c in TELEGRAM_CHATS if huella(c) not in saludados] if paises_conocidos else []
    if nuevos_chats:
        mejores = sorted((o for o in actuales.values() if pasa_filtros(o)),
                         key=lambda o: (-o["descuento"], o["ahora"]))
        paises = " y ".join(TIENDA[p] for p in ("do", "es") if any(o["pais"] == p for o in actuales.values()))
        for chat in nuevos_chats:
            canal = chat.startswith(("@", "-"))
            notificar(f"✅ <b>{'Canal conectado' if canal else 'Avisos activados'}</b> ({fecha})\n"
                      f"{'Aquí se publicarán' if canal else 'Aquí te llegarán'} las ofertas de {paises}: "
                      + (f"rebajas del {DESCUENTO_MINIMO:.0f}% o más" if DESCUENTO_MINIMO > 0 else "todas las rebajas")
                      + (" y últimas unidades" if INCLUIR_ULTIMAS else "")
                      + ", en cuanto aparezcan.\n\nAhora mismo, las mayores rebajas:",
                      mejores[:min(MAX_FOTOS, 5)], chats=[chat])
    saludados |= {huella(c) for c in TELEGRAM_CHATS}

    if avisar:
        n = len(avisar)
        por_pais = " · ".join(f"{TIENDA[p].split()[0]} {sum(1 for o in avisar if o['pais'] == p)}"
                              for p in ("do", "es") if any(o["pais"] == p for o in avisar))
        notificar(f"🛒 <b>{MARCA}: {n} {'novedad' if n == 1 else 'novedades'}</b> "
                  f"({por_pais}) · {fecha}", avisar)

    # Camas y colchones: lo nuevo, aunque no llegue al mínimo general (lo que ya salió arriba no se repite).
    if CAMA_Y_COLCHON:
        ya_avisados = {id(o) for o in avisar}
        camas = sorted((o for o in novedades if para_mi_cama(o) and id(o) not in ya_avisados),
                       key=lambda o: (-o["descuento"], o["ahora"]))
        if camas:
            n = len(camas)
            notificar(f"🛏️ <b>Tu cama y colchón ({tamanos}): {n} {'rebaja nueva' if n == 1 else 'rebajas nuevas'}</b> "
                      f"· {fecha}", camas, minimo=CAMA_DESCUENTO_MINIMO)

    # Cuántos productos se avisaron hoy (para el resumen de la noche).
    avisos_hoy = dict((estado or {}).get("avisos_hoy") or {})
    if avisos_hoy.get("fecha") != hoy:
        avisos_hoy = {"fecha": hoy, "n": 0}
    avisos_hoy["n"] += len(avisar) + (len(camas) if CAMA_Y_COLCHON else 0)

    # Resumen del día, una vez cada noche.
    resumen_enviado = (estado or {}).get("resumen_diario", "")
    if (RESUMEN_DIARIO and TELEGRAM_TOKEN and TELEGRAM_CHATS and resumen_enviado != hoy
            and ahora_rd.hour >= RESUMEN_HORA):
        medianoche_utc = (datetime(ahora_rd.year, ahora_rd.month, ahora_rd.day, tzinfo=HORA_RD)
                          .astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"))
        cuentas = revisiones_de_hoy(medianoche_utc)
        n_a = sum(1 for o in actuales.values() if o["pais"] == "do")
        n_b = sum(1 for o in actuales.values() if o["pais"] == "es")
        lineas = [f"✅ <b>Resumen del día</b> ({ahora_rd.strftime('%d/%m/%Y')})"]
        if cuentas:
            r, f = cuentas
            lineas.append(f"Sigo funcionando: hoy hice {r} revisiones"
                          + (f" ({f} con error)" if f else ", todas bien") + ".")
        else:
            lineas.append("Sigo funcionando.")
        n = avisos_hoy["n"]
        lineas.append(f"Avisos enviados hoy: {n}" + ("" if n else " (no hubo rebajas nuevas que cumplan tus reglas)"))
        lineas.append(f"Ahora vigilo: {TIENDA['do']} {n_a:,} ofertas · {TIENDA['es']} {n_b:,} ofertas")
        if CAMA_Y_COLCHON:
            n_camas = sum(1 for o in actuales.values() if para_mi_cama(o))
            lineas.append(f"🛏️ Camas y colchones {tamanos} en oferta ahora: {n_camas}")
        for chat in TELEGRAM_CHATS:
            enviar_texto(chat, "\n".join(lineas))
        resumen_enviado = hoy

    # Guardar estado (solo si los mensajes se enviaron bien; si falló algo,
    # el programa ya se detuvo y la próxima vez lo vuelve a intentar).
    limite = (ahora_rd - timedelta(days=DIAS_OLVIDO)).strftime("%Y-%m-%d")
    nuevo = {k: v for k, v in conocidos.items() if v.get("visto", "") >= limite}
    for clave, o in actuales.items():
        nuevo[clave] = {"precio": o["ahora"], "visto": hoy}
        if o["ultimas"]:
            nuevo[clave]["ultimas"] = True
        # La marca de "destacado" se recuerda unos días: si un día la lista no carga
        # (o carga a medias), no se vuelve a avisar de todo cuando vuelva.
        anterior = (conocidos.get(clave) or {}).get("destacado")
        if o["destacado"]:
            nuevo[clave]["destacado"] = hoy
        elif isinstance(anterior, str) and anterior >= limite:
            nuevo[clave]["destacado"] = anterior
    # Sin hora dentro del archivo: así solo cambia (y se guarda en GitHub)
    # cuando de verdad cambia algo, no en cada revisión.
    with open(ARCHIVO_ESTADO, "w", encoding="utf-8") as f:
        json.dump({"avisos_hoy": avisos_hoy, "resumen_diario": resumen_enviado,
                   "canales": dict(sorted(canales.items())), "chats_saludados": sorted(saludados),
                   "resumen_desde": resumen_desde,
                   "secciones_activadas": sorted(secciones_activadas),
                   "productos": dict(sorted(nuevo.items()))},
                  f, ensure_ascii=False, indent=1)
    log("Listo.")


if __name__ == "__main__":
    main()
