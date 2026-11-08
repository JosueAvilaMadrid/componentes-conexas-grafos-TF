"use strict";

/* ==========================================================================
   MOTOR MATEMÁTICO · Componentes conexas de un grafo dirigido
   Solo lógica pura: sin DOM, sin eventos.
   Convención: los índices de filas/columnas (orden, nuevos, bloques) son
   base 0; los nodos dentro de `componentes` son base 1 (igual que en Python),
   es decir, etiquetas[nodo - 1] es el nombre del nodo.
   ========================================================================== */

/* ============ 1. ESTADO GLOBAL ============ */
let n = 6;
let matriz = [];
let etiquetas = [];
let posiciones = null;

// Modo edición in-place: respaldo del grafo mientras se edita (ver sección "MODO EDICIÓN" al final)
let matriz_backup = null;
let etiquetas_backup = null;
let posiciones_backup = null;
let modoEdicionActivo = false;

/* ============ UTILIDADES ============ */
const copiarMatriz = (M) => M.map((fila) => fila.slice());

function validarNodos(nodos) {
  if (!Number.isInteger(nodos) || nodos < 4 || nodos > 12) {
    throw new RangeError("El número de nodos debe ser un entero en [4, 12].");
  }
}

/** Posiciones iniciales en círculo (primer nodo arriba), como fracciones [0, 1]. */
function posicionesEnCirculo(nodos) {
  return Array.from({ length: nodos }, (_, i) => {
    const angulo = (2 * Math.PI * i) / nodos - Math.PI / 2;
    return [0.5 + 0.4 * Math.cos(angulo), 0.5 + 0.4 * Math.sin(angulo)];
  });
}

/* ============ 2. CONSTRUCCIÓN DEL GRAFO ============ */

/** Matriz de ceros y etiquetas "1", "2", ... Actualiza el estado global. */
function crearGrafoVacio(nodos) {
  validarNodos(nodos);
  n = nodos;
  matriz = Array.from({ length: n }, () => new Array(n).fill(0));
  etiquetas = Array.from({ length: n }, (_, i) => String(i + 1));
  posiciones = posicionesEnCirculo(n);
  return { matriz, etiquetas };
}

/** Aristas al azar (0/1) con la diagonal en cero. `densidad` = probabilidad de un 1 (0.5 como en Python). */
function crearGrafoAleatorio(nodos, densidad = 0.5) {
  crearGrafoVacio(nodos);
  for (let i = 0; i < n; i++) {
    for (let j = 0; j < n; j++) {
      if (i === j) continue;
      matriz[i][j] = Math.random() < densidad ? 1 : 0;
    }
  }
  return { matriz, etiquetas };
}

/* ============ 3. PRODUCTO BOOLEANO ============ */

/** C[i][j] = 1 si existe t con A[i][t] = 1 y B[t][j] = 1 (equivale a (A·B) > 0). */
function productoBooleano(A, B) {
  const total = A.length;
  const C = Array.from({ length: total }, () => new Array(total).fill(0));
  for (let i = 0; i < total; i++) {
    for (let j = 0; j < total; j++) {
      for (let t = 0; t < total; t++) {
        if (A[i][t] === 1 && B[t][j] === 1) {
          C[i][j] = 1;
          break;
        }
      }
    }
  }
  return C;
}

/* ============ 4. PROCEDIMIENTO PASO A PASO ============ */

/** Paso 1: copia de la matriz con 1's en la diagonal principal. */
function matrizConDiagonal(M) {
  const M1 = copiarMatriz(M);
  for (let i = 0; i < M1.length; i++) M1[i][i] = 1;
  return M1;
}

/** Paso 2: potencias M^2, M^3, ... guardando los 1's nuevos hasta que se estabiliza. */
function potenciasConPasos(M) {
  const total = M.length;
  const M1 = matrizConDiagonal(M);
  const iteraciones = [];
  let anterior = copiarMatriz(M1);

  for (let exponente = 2; exponente <= total + 1; exponente++) {
    const potencia = productoBooleano(anterior, M1);
    const nuevos = [];

    for (let i = 0; i < total; i++) {
      for (let j = 0; j < total; j++) {
        if (potencia[i][j] === 1 && anterior[i][j] === 0) {
          // Nodo intermedio: i llega a t y desde t hay una arista hacia j
          let intermedio = 0;
          for (let t = 0; t < total; t++) {
            if (anterior[i][t] === 1 && M1[t][j] === 1) {
              intermedio = t;
              break;
            }
          }
          nuevos.push([i, j, intermedio]);
        }
      }
    }

    const estable = nuevos.length === 0;
    iteraciones.push({ exponente, matriz: potencia, nuevos, estable });
    if (estable) break;
    anterior = potencia;
  }
  return { M1, iteraciones };
}

/** Matriz de caminos M_R∞: potencias booleanas de M (con diagonal) hasta que no cambian. */
function matrizDeCaminos(M) {
  const total = M.length;
  const M1 = matrizConDiagonal(M);
  let potencia = copiarMatriz(M1);
  for (let k = 0; k < total; k++) {
    const siguiente = productoBooleano(potencia, M1);
    const igual = siguiente.every((fila, i) => fila.every((v, j) => v === potencia[i][j]));
    if (igual) break;
    potencia = siguiente;
  }
  return potencia;
}

/**
 * Paso 3: orden de filas por cantidad de 1's (mayor a menor). Desempates:
 *  1) el primer 1 más cerca de la primera columna (como en Python);
 *  2) la fila completa, comparada de izquierda a derecha (un 1 antes que un 0);
 *  3) el índice original.
 * El desempate 2 solo actúa cuando el 1 no decide y garantiza que las filas
 * idénticas (nodos de una misma componente) queden contiguas.
 */
function ordenarPorFilas(R) {
  const indices = R.map((_, i) => i);
  const unos = (i) => R[i].reduce((suma, v) => suma + v, 0);
  const primerUno = (i) => R[i].indexOf(1);

  return indices.sort((a, b) => {
    if (unos(a) !== unos(b)) return unos(b) - unos(a);
    if (primerUno(a) !== primerUno(b)) return primerUno(a) - primerUno(b);
    for (let k = 0; k < R.length; k++) {
      if (R[a][k] !== R[b][k]) return R[b][k] - R[a][k];
    }
    return a - b;
  });
}

/** Componentes: nodos (base 1) que se alcanzan mutuamente, es decir R[i][j] = 1 y R[j][i] = 1. */
function componentesConexas(M, R = matrizDeCaminos(M)) {
  const total = M.length;
  const visitados = new Array(total).fill(false);
  const componentes = [];

  for (let i = 0; i < total; i++) {
    if (visitados[i]) continue;
    const componente = [];
    for (let j = 0; j < total; j++) {
      if (R[i][j] === 1 && R[j][i] === 1) {
        componente.push(j + 1);
        visitados[j] = true;
      }
    }
    componentes.push(componente);
  }
  return componentes;
}

/** Límites [inicio, fin] (base 0, inclusivos) de cada bloque diagonal según el orden final. */
function calcularBloques(orden, componentes) {
  const total = orden.length;
  const compDeNodo = {};
  componentes.forEach((comp, idx) => comp.forEach((nodo) => { compDeNodo[nodo] = idx; }));

  const bloques = [];
  let inicio = 0;
  let compActual = compDeNodo[orden[0] + 1];

  for (let pos = 1; pos <= total; pos++) {
    if (pos === total || compDeNodo[orden[pos] + 1] !== compActual) {
      bloques.push([inicio, pos - 1]);
      if (pos < total) {
        compActual = compDeNodo[orden[pos] + 1];
        inicio = pos;
      }
    }
  }
  return bloques;
}

/**
 * Procedimiento completo (Pasos 1 a 4). Devuelve:
 *  M1           Paso 1: matriz con diagonal de 1's
 *  iteraciones  Paso 2: [{ exponente, matriz, nuevos: [[i, j, intermedio]], estable }]
 *  R            Paso 2: matriz de caminos final
 *  orden        Paso 3: índices de fila (base 0) ordenados
 *  R_filas      Paso 3: R con las filas reordenadas
 *  R_final      Paso 4: R con filas y columnas reordenadas
 *  componentes  Paso 4: [[nodos base 1], ...]
 *  bloques      Paso 4: [[inicio, fin], ...] sobre R_final
 */
function calcularProcedimiento(M) {
  const total = M.length;
  const { M1, iteraciones } = potenciasConPasos(M);
  const R = matrizDeCaminos(M);

  const orden = ordenarPorFilas(R);
  const R_filas = orden.map((i) => R[i].slice());
  const R_final = orden.map((i) => orden.map((j) => R[i][j]));

  const componentes = componentesConexas(M, R);
  const bloques = calcularBloques(orden, componentes);

  return { M1, iteraciones, R, orden, R_filas, R_final, componentes, bloques };
}


/* ==========================================================================
   INTERFAZ · navegación, matriz, canvas y eventos
   (asume que el motor matemático de arriba ya está definido)
   ========================================================================== */

const $ = (id) => document.getElementById(id);

/* ============ ESTADO DE LA INTERFAZ ============ */
let procedimiento = null;          // resultado de calcularProcedimiento(matriz)
let modoConstruccion = "manual";   // "manual" | "aleatorio"

const LADO = 640;                  // coordenadas lógicas del lienzo (px)
const RADIO_NODO = 22;
const LARGO_PUNTA = 13;
const COLOR_ESTRUCTURA = "#25133E";   // morado profundo: líneas, bordes y texto
const COLOR_ACENTO = "#9F53FF";       // morado vibrante: resaltado de nodos y flecha de guía
const COLOR_NODO = "#7F2BE0";         // color base de todos los nodos en la pantalla de edición

/** Ajusta la resolución interna del canvas a pantallas retina sin cambiar su tamaño en CSS. */
function prepararLienzo(canvas) {
  const dpr = Math.min(window.devicePixelRatio || 1, 2);
  canvas.width = LADO * dpr;
  canvas.height = LADO * dpr;
  const c = canvas.getContext("2d");
  c.setTransform(dpr, 0, 0, dpr, 0, 0);
  return c;
}

const lienzo = $("lienzo-grafo");
const ctx = prepararLienzo(lienzo);

/* ============ 1. NAVEGACIÓN SPA Y STEPPER ============ */
const IDS_PANTALLAS = ["pantalla-inicio", "pantalla-edicion", "pantalla-pasos"];

function mostrarPantalla(paso) {
  detenerReproduccion();       // si salimos de la pantalla 3, se detiene la reproducción automática
  IDS_PANTALLAS.forEach((id, k) => $(id).classList.toggle("oculto", k !== paso - 1));

  document.querySelectorAll("#stepper .stepper__item").forEach((item) => {
    const p = Number(item.dataset.paso);
    item.classList.toggle("activo", p === paso);
    item.classList.toggle("hecho", p < paso);
    if (p === paso) item.setAttribute("aria-current", "step");
    else item.removeAttribute("aria-current");
  });

  window.scrollTo({ top: 0 });
}

function mostrarPantallaInicio() {
  mostrarPantalla(1);
}

function mostrarPantallaEdicion() {
  mostrarPantalla(2);
  modoEdicionActivo = false;       // la pantalla siempre se abre con el grafo bloqueado
  matriz_backup = etiquetas_backup = posiciones_backup = null;
  aplicarModoHerramienta("aristas");   // herramienta por defecto: aristas (Mover nodos apagado)
  aplicarEstadoEdicion();          // actualiza texto, botones, matriz y grafo
}

function mostrarPantallaPasos() {
  mostrarPantalla(3);
  iniciarPasos();
}

const AYUDA_HERRAMIENTA = {
  aristas: "Arrastra desde un nodo hasta otro: si la arista no existe se crea y, si ya existe, se quita. Haz clic sobre un nodo (o suéltalo sobre sí mismo) para crear o quitar un bucle. Activa «Mover nodos» para acomodarlos.",
  mover: "Arrastra los nodos para acomodarlos. Vuelve a presionar «Mover nodos» para regresar a las aristas.",
};

function actualizarTextoModo() {
  const base = modoConstruccion === "aleatorio" ? "Grafo aleatorio generado." : "Modo manual: la matriz empieza vacía.";
  const ayuda = modoEdicionActivo
    ? `Modo edición: haz clic en las celdas de la matriz (fila → columna). ${AYUDA_HERRAMIENTA[lienzo.dataset.modo] || ""} Aceptar conserva los cambios y Cancelar los descarta.`
    : "Presiona «Editar Matriz y Gráfico» para modificar las conexiones.";
  $("texto-modo").textContent = `${base} ${ayuda}`.trim();
}

/* ============ 2. MATRIZ DE ADYACENCIA ============ */

/**
 * Construye el DOM de una matriz con etiquetas de filas y columnas.
 * opciones: { editable, nuevos, diagonal, bloques } (los tres últimos son Set de "i,j").
 */
function crearMatrizDOM(M, etqFilas, etqColumnas, opciones = {}) {
  const { editable = false, nuevos = new Set(), diagonal = new Set(), bloques = new Set() } = opciones;
  const columnas = M[0].length;

  const marco = document.createElement("div");
  marco.className = "matriz-marco";
  marco.style.setProperty("--cols", columnas + 1);

  const rejilla = document.createElement("div");
  rejilla.className = "matriz";

  const nuevaCelda = (texto, clase) => {
    const celda = document.createElement("div");
    celda.className = clase;
    celda.textContent = texto;
    return celda;
  };

  rejilla.appendChild(nuevaCelda("", "celda celda--esquina"));
  etqColumnas.forEach((e) => rejilla.appendChild(nuevaCelda(e, "celda celda--etq")));

  M.forEach((fila, i) => {
    rejilla.appendChild(nuevaCelda(etqFilas[i], "celda celda--etq"));
    fila.forEach((valor, j) => {
      const clave = `${i},${j}`;
      let clase = "celda";
      if (nuevos.has(clave)) clase += " celda--nuevo";
      else if (diagonal.has(clave)) clase += " celda--diag";
      else if (valor === 1) clase += " celda--uno";
      if (bloques.has(clave)) clase += " celda--bloque";

      if (editable) clase += " celda--editable";
      const celda = nuevaCelda(valor, clase);
      celda.dataset.i = i;
      celda.dataset.j = j;

      if (editable) {
        celda.tabIndex = 0;
        celda.setAttribute("role", "button");
        celda.setAttribute("aria-label", i === j
          ? `Bucle de ${etqFilas[i]} hacia sí mismo: ${valor}`
          : `Arista de ${etqFilas[i]} hacia ${etqColumnas[j]}: ${valor}`);
      }
      rejilla.appendChild(celda);
    });
  });

  marco.appendChild(rejilla);
  return marco;
}

/** Lee n, matriz y etiquetas y dibuja la tabla editable dentro de #contenedor-matriz. */
function renderizarMatriz() {
  $("contenedor-matriz").replaceChildren(crearMatrizDOM(matriz, etiquetas, etiquetas, { editable: modoEdicionActivo }));
  actualizarSelectAnalisis();      // el selector de análisis siempre refleja los nodos y nombres actuales
}

/** Alterna 0/1 de una celda (la diagonal incluida: un 1 en (i, i) es un bucle) y actualiza tabla y lienzo. */
function alternarArista(i, j, conTeclado = false) {
  matriz[i][j] = matriz[i][j] === 1 ? 0 : 1;
  renderizarMatriz();
  dibujarGrafo();
  if (conTeclado) {
    const celda = $("contenedor-matriz").querySelector(`[data-i="${i}"][data-j="${j}"]`);
    if (celda) celda.focus();
  }
}

function alActivarCelda(e) {
  if (!modoEdicionActivo) return;
  const celda = e.target.closest(".celda--editable");
  if (!celda) return;
  if (e.type === "keydown") {
    if (e.key !== "Enter" && e.key !== " ") return;
    e.preventDefault();
  }
  alternarArista(Number(celda.dataset.i), Number(celda.dataset.j), e.type === "keydown");
}

/* ============ 3. MOTOR DEL CANVAS ============ */

/**
 * Geometría de una flecha entre dos centros (px). Si hay arista recíproca se curva
 * hacia un lado para que ambas se distingan. La punta queda sobre el borde del nodo destino.
 */
function geometriaFlecha([x1, y1], [x2, y2], reciproca) {
  const dx = x2 - x1;
  const dy = y2 - y1;
  const dist = Math.hypot(dx, dy);
  if (dist < 2 * RADIO_NODO + 4) return null;      // nodos casi superpuestos

  const curva = reciproca ? 26 : 0;
  const cx = (x1 + x2) / 2 - (dy / dist) * curva;  // punto de control (normal a la recta)
  const cy = (y1 + y2) / 2 + (dx / dist) * curva;

  // Vectores unitarios desde cada centro hacia el punto de control
  const vl = Math.hypot(cx - x1, cy - y1);
  const wl = Math.hypot(cx - x2, cy - y2);
  const vx = (cx - x1) / vl, vy = (cy - y1) / vl;
  const wx = (cx - x2) / wl, wy = (cy - y2) / wl;

  const inicio = [x1 + vx * RADIO_NODO, y1 + vy * RADIO_NODO];
  const punta = [x2 + wx * RADIO_NODO, y2 + wy * RADIO_NODO];   // toca el borde del destino
  const base = [punta[0] + wx * LARGO_PUNTA * 0.85, punta[1] + wy * LARGO_PUNTA * 0.85];
  const angulo = Math.atan2(-wy, -wx);                          // sentido de la flecha

  return { inicio, control: [cx, cy], punta, base, angulo };
}

function dibujarFlecha(c, p1, p2, reciproca) {
  const g = geometriaFlecha(p1, p2, reciproca);
  if (!g) return;

  c.strokeStyle = COLOR_ESTRUCTURA;
  c.fillStyle = COLOR_ESTRUCTURA;
  c.lineWidth = 2;
  c.beginPath();
  c.moveTo(g.inicio[0], g.inicio[1]);
  c.quadraticCurveTo(g.control[0], g.control[1], g.base[0], g.base[1]);
  c.stroke();

  dibujarPunta(c, g.punta, g.angulo);
}

/** Triángulo relleno (con el color de relleno actual) cuya punta está en `punta` y mira hacia `angulo`. */
function dibujarPunta(c, punta, angulo) {
  const abertura = Math.PI / 7;
  c.beginPath();
  c.moveTo(punta[0], punta[1]);
  c.lineTo(punta[0] - LARGO_PUNTA * Math.cos(angulo - abertura), punta[1] - LARGO_PUNTA * Math.sin(angulo - abertura));
  c.lineTo(punta[0] - LARGO_PUNTA * Math.cos(angulo + abertura), punta[1] - LARGO_PUNTA * Math.sin(angulo + abertura));
  c.closePath();
  c.fill();
}

/**
 * Bucle (self-loop): curva de Bézier que sale del borde del nodo, sobresale hacia la esquina superior
 * derecha y regresa al borde con una punta de flecha (mismo color y grosor que una arista normal).
 */
function dibujarBucle(c, [x, y], { color = COLOR_ESTRUCTURA, ancho = 2, discontinuo = false } = {}) {
  const direccion = -Math.PI / 4;                  // esquina superior derecha (el eje y del canvas crece hacia abajo)
  const salida = direccion - 0.55;                 // ángulo, sobre el borde del nodo, donde nace el bucle
  const llegada = direccion + 0.55;                // ángulo donde termina, con la punta de flecha
  const alcance = RADIO_NODO + 60;                 // qué tanto sobresalen los puntos de control
  const sobreBorde = (radio, angulo) => [x + radio * Math.cos(angulo), y + radio * Math.sin(angulo)];

  const inicio = sobreBorde(RADIO_NODO, salida);
  const control1 = sobreBorde(alcance, salida - 0.25);
  const control2 = sobreBorde(alcance, llegada + 0.25);
  const punta = sobreBorde(RADIO_NODO, llegada);   // la punta toca el borde exterior del nodo

  const largo = Math.hypot(punta[0] - control2[0], punta[1] - control2[1]);
  const ux = (punta[0] - control2[0]) / largo;     // sentido en el que la flecha llega al nodo
  const uy = (punta[1] - control2[1]) / largo;
  const base = [punta[0] - ux * LARGO_PUNTA * 0.85, punta[1] - uy * LARGO_PUNTA * 0.85];

  c.strokeStyle = color;
  c.fillStyle = color;
  c.lineWidth = ancho;
  if (discontinuo) c.setLineDash([7, 5]);
  c.beginPath();
  c.moveTo(inicio[0], inicio[1]);
  c.bezierCurveTo(control1[0], control1[1], control2[0], control2[1], base[0], base[1]);
  c.stroke();
  c.setLineDash([]);
  dibujarPunta(c, punta, Math.atan2(uy, ux));
}

/** Flecha provisional (discontinua) mientras el usuario arrastra para crear o quitar una arista. */
function dibujarFlechaVirtual(c, desde, hasta, color) {
  const dx = hasta[0] - desde[0];
  const dy = hasta[1] - desde[1];
  const largo = Math.hypot(dx, dy);
  if (largo < RADIO_NODO + LARGO_PUNTA + 2) return;     // aún muy cerca del nodo origen
  const ux = dx / largo;
  const uy = dy / largo;

  c.strokeStyle = color;
  c.fillStyle = color;
  c.lineWidth = 2.5;
  c.setLineDash([7, 5]);
  c.beginPath();
  c.moveTo(desde[0] + ux * RADIO_NODO, desde[1] + uy * RADIO_NODO);
  c.lineTo(hasta[0] - ux * LARGO_PUNTA * 0.85, hasta[1] - uy * LARGO_PUNTA * 0.85);
  c.stroke();
  c.setLineDash([]);
  dibujarPunta(c, hasta, Math.atan2(uy, ux));
}

/** Nodo como esfera 3D: gradiente radial con el brillo arriba a la izquierda y `colorBase` hacia el borde. */
function dibujarNodo(c, [x, y], texto, resaltado, colorBase) {
  const radio = RADIO_NODO;
  const gradiente = c.createRadialGradient(x - radio / 3, y - radio / 3, radio / 8, x, y, radio);
  gradiente.addColorStop(0, "#ffffff");       // brillo de luz
  gradiente.addColorStop(1, colorBase);       // color de sombra / base

  c.beginPath();
  c.arc(x, y, radio, 0, 2 * Math.PI);
  c.fillStyle = gradiente;
  c.fill();
  c.lineWidth = resaltado ? 4 : 2;
  c.strokeStyle = resaltado ? COLOR_ACENTO : COLOR_ESTRUCTURA;
  c.stroke();

  // Texto morado con un halo blanco fino: se lee sobre la parte clara y sobre la oscura de la esfera
  c.font = '700 16px Inter, system-ui, "Segoe UI", Arial, sans-serif';
  c.textAlign = "center";
  c.textBaseline = "middle";
  c.lineJoin = "round";
  c.lineWidth = 3;
  c.strokeStyle = "rgba(255, 255, 255, .92)";
  c.strokeText(texto, x, y + 1);
  c.fillStyle = COLOR_ESTRUCTURA;
  c.fillText(texto, x, y + 1);
}

/** Dibuja un grafo en cualquier contexto 2D (reutilizable para el lienzo de resultados). */
function trazarGrafo(c, M, etqs, pos, { resaltado = null, colorNodo = null } = {}) {
  c.clearRect(0, 0, LADO, LADO);
  const centros = pos.map(([fx, fy]) => [fx * LADO, fy * LADO]);
  const marcados = resaltado instanceof Set ? resaltado : new Set(resaltado === null ? [] : [resaltado]);

  for (let i = 0; i < M.length; i++) {
    for (let j = 0; j < M.length; j++) {
      if (M[i][j] !== 1) continue;
      if (i === j) dibujarBucle(c, centros[i]);                          // bucle: el nodo apunta a sí mismo
      else dibujarFlecha(c, centros[i], centros[j], M[j][i] === 1);
    }
  }
  // Nodos encima de las líneas
  centros.forEach((centro, i) => {
    dibujarNodo(c, centro, etqs[i], marcados.has(i), colorNodo ? colorNodo(i) : COLOR_NODO);
  });
}

function dibujarGrafo() {
  if (!posiciones || posiciones.length !== n) posiciones = posicionesEnCirculo(n);
  const conectando = nodoOrigen !== null;
  const marcados = new Set();
  if (nodoArrastrado !== null) marcados.add(nodoArrastrado);
  else if (conectando) {
    marcados.add(nodoOrigen);
    if (nodoHover !== null) marcados.add(nodoHover);
  } else if (nodoHover !== null) marcados.add(nodoHover);
  trazarGrafo(ctx, matriz, etiquetas, posiciones, { resaltado: marcados });

  // Flecha virtual: parte del nodo origen y sigue al cursor (o se ajusta al borde del nodo destino)
  if (conectando && puntoActual) {
    const desde = [posiciones[nodoOrigen][0] * LADO, posiciones[nodoOrigen][1] * LADO];
    // Cursor sobre el propio nodo de origen: soltar crea o quita un bucle, así que se muestra un bucle de guía
    if (nodoEn(puntoActual[0], puntoActual[1]) === nodoOrigen) {
      dibujarBucle(ctx, desde, { color: matriz[nodoOrigen][nodoOrigen] === 1 ? "#5B4F72" : COLOR_ACENTO, ancho: 2.5, discontinuo: true });
      return;
    }
    let hasta = puntoActual;
    if (nodoHover !== null && nodoHover !== nodoOrigen) {
      const centro = [posiciones[nodoHover][0] * LADO, posiciones[nodoHover][1] * LADO];
      const d = Math.hypot(desde[0] - centro[0], desde[1] - centro[1]) || 1;
      hasta = [centro[0] + ((desde[0] - centro[0]) / d) * RADIO_NODO, centro[1] + ((desde[1] - centro[1]) / d) * RADIO_NODO];
    }
    // Inteligente: gris si la arista ya existe (se va a quitar), morado vibrante si es nueva (se va a crear)
    const existe = nodoHover !== null && nodoHover !== nodoOrigen && matriz[nodoOrigen][nodoHover] === 1;
    dibujarFlechaVirtual(ctx, desde, hasta, existe ? "#5B4F72" : COLOR_ACENTO);
  }
}

/* ============ 4. DRAG & DROP DE NODOS ============ */
let nodoArrastrado = null;
let nodoOrigen = null;        // nodo desde el que se arrastra una flecha (modo aristas)
let puntoActual = null;       // posición del cursor mientras se arrastra la flecha virtual
let nodoHover = null;
let desfase = [0, 0];
let dibujoPendiente = false;

function solicitarDibujo() {
  if (dibujoPendiente) return;
  dibujoPendiente = true;
  requestAnimationFrame(() => {
    dibujoPendiente = false;
    dibujarGrafo();
  });
}

/** Coordenadas lógicas (0..LADO) de un evento de mouse o touch sobre el lienzo. */
function puntoDelEvento(e) {
  const t = (e.touches && e.touches[0]) || (e.changedTouches && e.changedTouches[0]) || e;
  const r = lienzo.getBoundingClientRect();
  return [((t.clientX - r.left) * LADO) / r.width, ((t.clientY - r.top) * LADO) / r.height];
}

function nodoEn(x, y) {
  if (!posiciones) return null;
  for (let i = posiciones.length - 1; i >= 0; i--) {
    if (Math.hypot(x - posiciones[i][0] * LADO, y - posiciones[i][1] * LADO) <= RADIO_NODO + 4) return i;
  }
  return null;
}

function alPresionar(e) {
  if (!modoEdicionActivo) return;
  if (e.cancelable && e.type === "touchstart") e.preventDefault();
  const [x, y] = puntoDelEvento(e);
  const i = nodoEn(x, y);
  if (i === null) return;

  const modo = lienzo.dataset.modo;
  if (modo === "aristas") {      // no se mueve el nodo: se arrastra una flecha virtual
    nodoOrigen = i;
    puntoActual = [x, y];
    nodoHover = null;
    solicitarDibujo();
    return;
  }

  nodoArrastrado = i;
  desfase = [posiciones[i][0] * LADO - x, posiciones[i][1] * LADO - y];
  lienzo.style.cursor = "grabbing";
  solicitarDibujo();
}

function alMover(e) {
  if (!modoEdicionActivo) return;      // bloqueado: sin arrastre ni resaltado de nodos
  const [x, y] = puntoDelEvento(e);

  if (nodoOrigen !== null) {
    if (e.cancelable) e.preventDefault();
    puntoActual = [x, y];
    const candidato = nodoEn(x, y);
    nodoHover = candidato !== nodoOrigen ? candidato : null;
    solicitarDibujo();
    return;
  }

  if (nodoArrastrado !== null) {
    if (e.cancelable) e.preventDefault();
    const limite = RADIO_NODO + 6;
    const nx = Math.min(Math.max(x + desfase[0], limite), LADO - limite);
    const ny = Math.min(Math.max(y + desfase[1], limite), LADO - limite);
    posiciones[nodoArrastrado] = [nx / LADO, ny / LADO];
    solicitarDibujo();
    return;
  }

  const hover = nodoEn(x, y);
  if (hover !== nodoHover) {
    nodoHover = hover;
    solicitarDibujo();
  }
}

function alSoltar(e) {
  if (nodoOrigen !== null) {
    const [x, y] = puntoDelEvento(e);
    const destino = nodoEn(x, y);
    if (destino !== null) {      // destino === nodoOrigen: crea o quita un bucle
      matriz[nodoOrigen][destino] = matriz[nodoOrigen][destino] === 1 ? 0 : 1;
      renderizarMatriz();
    }
    nodoOrigen = null;
    puntoActual = null;
    nodoHover = e.type === "mouseup" ? destino : null;
    solicitarDibujo();
    return;
  }

  nodoArrastrado = null;
  lienzo.style.cursor = "";
  if (e.type === "mouseup") {
    const [x, y] = puntoDelEvento(e);
    nodoHover = nodoEn(x, y);
  } else {
    nodoHover = null;
  }
  solicitarDibujo();
}

function alSalir() {
  nodoArrastrado = null;
  nodoOrigen = null;
  puntoActual = null;
  nodoHover = null;
  lienzo.style.cursor = "";
  solicitarDibujo();
}

/* ============ HERRAMIENTAS DEL LIENZO ============ */
/** Fija el modo del lienzo ("aristas" o "mover") y sincroniza botón, cursor, texto y dibujo. */
function aplicarModoHerramienta(modo) {
  lienzo.dataset.modo = modo;
  document.querySelectorAll(".btn--herramienta[data-modo]").forEach((boton) => {
    boton.setAttribute("aria-pressed", String(boton.dataset.modo === modo));
  });
  nodoArrastrado = null;
  nodoOrigen = null;
  puntoActual = null;
  nodoHover = null;
  lienzo.style.cursor = "";
  actualizarTextoModo();
  solicitarDibujo();
}

/** Toggle: si la herramienta pulsada ya está activa se apaga y se vuelve a "aristas"; si no, se activa. */
function cambiarModoHerramienta(modo) {
  aplicarModoHerramienta(lienzo.dataset.modo === modo ? "aristas" : modo);
}

/** Deja la matriz en ceros (se conservan los nodos y su posición). */
function limpiarGrafo() {
  matriz.forEach((fila) => fila.fill(0));
  renderizarMatriz();
  dibujarGrafo();
  mostrarToast("Se quitaron todas las aristas.");
}

/** Nueva matriz aleatoria con la misma cantidad de nodos; conserva posiciones y nombres. */
function regenerarGrafo() {
  const posicionesPrevias = posiciones;
  const etiquetasPrevias = etiquetas;
  crearGrafoAleatorio(n);
  if (posicionesPrevias && posicionesPrevias.length === n) posiciones = posicionesPrevias;
  etiquetas = etiquetasPrevias;
  modoConstruccion = "aleatorio";
  actualizarTextoModo();
  renderizarMatriz();
  dibujarGrafo();
}

function inicializarHerramientas() {
  document.querySelectorAll(".btn--herramienta[data-modo]").forEach((boton) => {
    boton.addEventListener("click", () => cambiarModoHerramienta(boton.dataset.modo));
  });
  $("btn-limpiar").addEventListener("click", () => pedirConfirmacion(
    "¿Estás seguro de que deseas borrar todas las aristas? Esta acción no se puede deshacer.",
    limpiarGrafo
  ));
  $("btn-regenerar").addEventListener("click", () => pedirConfirmacion(
    "¿Estás seguro? Se creará un grafo al azar y perderás el actual si no lo has guardado.",
    regenerarGrafo
  ));
}

/* ============ 5. SELECTOR DE NODOS Y BOTONES BASE ============ */
function fijarNodosElegidos(valor) {
  const v = Math.min(12, Math.max(4, Math.round(Number(valor))));
  $("input-n").value = v;
  $("rango-n").value = v;
  return v;
}

function leerNodosElegidos() {
  const crudo = parseInt($("input-n").value, 10);
  return fijarNodosElegidos(Number.isNaN(crudo) ? $("rango-n").value : crudo);
}

function inicializarApp() {
  // Selector de cantidad de nodos
  $("input-n").addEventListener("input", () => {
    const v = parseInt($("input-n").value, 10);
    if (v >= 4 && v <= 12) $("rango-n").value = v;
  });
  $("input-n").addEventListener("change", leerNodosElegidos);
  $("rango-n").addEventListener("input", () => fijarNodosElegidos($("rango-n").value));
  $("btn-menos").addEventListener("click", () => fijarNodosElegidos(leerNodosElegidos() - 1));
  $("btn-mas").addEventListener("click", () => fijarNodosElegidos(leerNodosElegidos() + 1));

  // Modo de construcción
  $("btn-aleatorio").addEventListener("click", () => {
    crearGrafoAleatorio(leerNodosElegidos());
    modoConstruccion = "aleatorio";
    mostrarPantallaEdicion();
  });
  $("btn-manual").addEventListener("click", () => {
    crearGrafoVacio(leerNodosElegidos());
    modoConstruccion = "manual";
    mostrarPantallaEdicion();
  });

  // Matriz editable (delegación de eventos)
  $("contenedor-matriz").addEventListener("click", alActivarCelda);
  $("contenedor-matriz").addEventListener("keydown", alActivarCelda);

  // Drag & drop en el lienzo (mouse + touch para móviles)
  lienzo.addEventListener("mousedown", alPresionar);
  lienzo.addEventListener("mousemove", alMover);
  lienzo.addEventListener("mouseup", alSoltar);
  lienzo.addEventListener("mouseleave", alSalir);
  lienzo.addEventListener("touchstart", alPresionar, { passive: false });
  lienzo.addEventListener("touchmove", alMover, { passive: false });
  lienzo.addEventListener("touchend", alSoltar);
  lienzo.addEventListener("touchcancel", alSalir);

  // Ejecución y navegación
  $("btn-ejecutar").addEventListener("click", () => {
    procedimiento = calcularProcedimiento(matriz);
    mostrarPantallaPasos();
  });
  $("btn-volver-inicio").addEventListener("click", () => pedirConfirmacion(
    "¿Estás seguro de que deseas volver al inicio? El grafo actual se perderá si no lo has guardado.",
    mostrarPantallaInicio
  ));
  $("btn-nuevo").addEventListener("click", () => pedirConfirmacion(
    "¿Estás seguro de que deseas volver al inicio? El grafo actual se perderá si no lo has guardado.",
    mostrarPantallaInicio
  ));

  inicializarHerramientas();
}

inicializarApp();


/* ==========================================================================
   FUNCIONALIDADES AVANZADAS · almacenamiento local, PDF y QR
   (sin backend: todo ocurre en el navegador)
   ========================================================================== */

/* ============ UTILIDADES ============ */
const CLAVE_EJERCICIOS = "componentesConexas.ejercicios.v1";
const URL_QRCODEJS = "https://cdnjs.cloudflare.com/ajax/libs/qrcodejs/1.0.0/qrcode.min.js";
const IDS_MODALES = ["modal-qr", "modal-guardados", "modal-compartir", "modal-manual", "modal-confirmacion", "modal-api-key", "modal-aviso"];
const PALETA_COMPONENTES = [          // color base de cada componente (tonos saturados para el efecto 3D)
  "#3B82F6", "#F59E0B", "#10B981", "#EF4444", "#8B5CF6", "#14B8A6",
  "#EC4899", "#84CC16", "#6366F1", "#F97316", "#0EA5E9", "#A16207",
];

/** Crea un elemento: props admite className, texto, estilo y cualquier atributo; hijos se anexan. */
function crearElemento(etiqueta, props = {}, ...hijos) {
  const el = document.createElement(etiqueta);
  Object.entries(props).forEach(([clave, valor]) => {
    if (clave === "className") el.className = valor;
    else if (clave === "texto") el.textContent = valor;
    else if (clave === "estilo") el.style.cssText = valor;
    else el.setAttribute(clave, valor);
  });
  hijos.forEach((h) => el.append(h));
  return el;
}

let temporizadorToast = null;
function mostrarToast(texto) {
  const toast = $("toast");
  toast.textContent = texto;
  toast.classList.remove("oculto");
  clearTimeout(temporizadorToast);
  temporizadorToast = setTimeout(() => toast.classList.add("oculto"), 2800);
}

let focoPrevio = null;
function abrirModal(id) {
  focoPrevio = document.activeElement;
  const modal = $(id);
  modal.classList.remove("oculto");
  const foco = modal.querySelector("button, input");
  if (foco) foco.focus();
}

function cerrarModal(id) {
  const modal = $(id);
  if (!modal) return;
  modal.classList.add("oculto");
  if (focoPrevio && focoPrevio.focus) focoPrevio.focus();
}

/* ---------- Modal de confirmación (sustituye a window.confirm) ---------- */
let accionPendiente = null;

/** Muestra `mensaje` y ejecuta `accion` solo si el usuario presiona Aceptar. */
function pedirConfirmacion(mensaje, accion) {
  $("texto-confirmacion").textContent = mensaje;
  accionPendiente = accion;
  abrirModal("modal-confirmacion");
  $("btn-confirmar-cancelar").focus();      // el foco empieza en Cancelar: Enter no confirma por accidente
}

function aceptarConfirmacion() {
  const accion = accionPendiente;
  accionPendiente = null;
  cerrarModal("modal-confirmacion");
  if (accion) accion();
}

function cancelarConfirmacion() {
  accionPendiente = null;
  cerrarModal("modal-confirmacion");
}

const scriptsCargados = {};
/** Inyecta un <script> externo una sola vez y devuelve una promesa. */
function cargarScript(url) {
  if (!scriptsCargados[url]) {
    scriptsCargados[url] = new Promise((resolver, rechazar) => {
      const script = document.createElement("script");
      script.src = url;
      script.onload = resolver;
      script.onerror = () => {
        delete scriptsCargados[url];
        script.remove();
        rechazar(new Error("No se pudo cargar " + url));
      };
      document.head.appendChild(script);
    });
  }
  return scriptsCargados[url];
}

/* ============ CODEC_INICIO · validación y formato del QR ============ */

/** Valida y normaliza un grafo venga de localStorage o de un QR. Lanza Error con mensaje legible. */
function normalizarGrafo(datos) {
  const M = datos && datos.matriz;
  if (!Array.isArray(M) || M.length < 4 || M.length > 12) {
    throw new Error("El grafo debe tener entre 4 y 12 nodos.");
  }
  const nn = M.length;
  if (!M.every((fila) => Array.isArray(fila) && fila.length === nn)) {
    throw new Error("La matriz de adyacencia no es cuadrada.");
  }

  const matrizOk = M.map((fila, i) => fila.map((v, j) => {
    if (v !== 0 && v !== 1) throw new Error("La matriz solo puede contener 0 y 1.");
    return v;
  }));

  const etiquetasOk = Array.isArray(datos.etiquetas) && datos.etiquetas.length === nn
    ? datos.etiquetas.map((e) => String(e).trim().slice(0, 4))
    : Array.from({ length: nn }, (_, i) => String(i + 1));

  const posValidas = Array.isArray(datos.posiciones) && datos.posiciones.length === nn &&
    datos.posiciones.every((p) => Array.isArray(p) && p.length === 2 && p.every((v) => Number.isFinite(v)));
  const posicionesOk = posValidas
    ? datos.posiciones.map(([x, y]) => [Math.min(0.95, Math.max(0.05, x)), Math.min(0.95, Math.max(0.05, y))])
    : posicionesEnCirculo(nn);

  return { n: nn, matriz: matrizOk, etiquetas: etiquetasOk, posiciones: posicionesOk };
}

const bitsAHex = (bits) => {
  let hex = "";
  for (let i = 0; i < bits.length; i += 4) hex += parseInt(bits.slice(i, i + 4).padEnd(4, "0"), 2).toString(16);
  return hex;
};
const hexABits = (hex) => [...hex].map((c) => parseInt(c, 16).toString(2).padStart(4, "0")).join("");

/**
 * Estado actual -> JSON compacto: [versión, n, aristas en hex, posiciones en base 36, etiquetas?]
 * Versión 1: los n·(n-1) bits fuera de la diagonal (grafo sin bucles, compatible con versiones anteriores).
 * Versión 2: los n·n bits, diagonal incluida (solo si hay algún bucle). Cada coordenada ocupa 2 caracteres base 36.
 */
function codificarGrafoParaQR() {
  const conBucles = matriz.some((fila, i) => fila[i] === 1);
  let bits = "";
  for (let i = 0; i < n; i++) {
    for (let j = 0; j < n; j++) {
      if (conBucles || i !== j) bits += matriz[i][j] ? "1" : "0";
    }
  }
  const pos = (posiciones && posiciones.length === n ? posiciones : posicionesEnCirculo(n))
    .map((p) => p.map((v) => Math.round(Math.min(1, Math.max(0, v)) * 1295).toString(36).padStart(2, "0")).join(""))
    .join("");

  const datos = [conBucles ? 2 : 1, n, bitsAHex(bits), pos];
  if (etiquetas.some((e, i) => e !== String(i + 1))) datos.push(etiquetas);   // solo si hay nombres propios
  return JSON.stringify(datos);
}

/** Texto de un QR -> grafo normalizado. Acepta el formato compacto y el JSON de la versión Python. */
function decodificarGrafoDeQR(texto) {
  let datos;
  try {
    datos = JSON.parse(String(texto).replace(/^\uFEFF/, "").trim());
  } catch (e) {
    throw new Error("El código QR no contiene un formato JSON válido.");
  }

  if (Array.isArray(datos)) {
    const [version, nn, hex, pos, etqs] = datos;
    if ((version !== 1 && version !== 2) || !Number.isInteger(nn) || nn < 4 || nn > 12 || typeof hex !== "string" || !/^[0-9a-f]*$/i.test(hex)) {
      throw new Error("El código QR no pertenece a un ejercicio de esta aplicación.");
    }
    const conBucles = version === 2;                              // versión 2: la diagonal (bucles) viene incluida
    const total = conBucles ? nn * nn : nn * (nn - 1);
    const bits = hexABits(hex).slice(0, total);
    if (bits.length !== total) throw new Error("El código QR está incompleto o dañado.");

    let k = 0;
    const M = Array.from({ length: nn }, (_, i) => Array.from({ length: nn }, (_, j) => (i === j && !conBucles ? 0 : Number(bits[k++]))));
    const pos2 = typeof pos === "string" && pos.length === 4 * nn
      ? Array.from({ length: nn }, (_, i) => [
          parseInt(pos.substr(4 * i, 2), 36) / 1295,
          parseInt(pos.substr(4 * i + 2, 2), 36) / 1295,
        ])
      : null;
    return normalizarGrafo({ matriz: M, etiquetas: etqs, posiciones: pos2 });
  }

  if (datos && typeof datos === "object" && datos.matriz) return normalizarGrafo(datos);   // formato de la versión Python
  throw new Error("El código QR no pertenece a un ejercicio de esta aplicación.");
}
/* ============ CODEC_FIN ============ */

/** Reemplaza el estado global por un grafo ya normalizado y abre la pantalla de edición. */
function aplicarGrafo(grafo) {
  n = grafo.n;
  matriz = grafo.matriz;
  etiquetas = grafo.etiquetas;
  posiciones = grafo.posiciones;
  procedimiento = null;
  modoConstruccion = "manual";
  fijarNodosElegidos(n);
  mostrarPantallaEdicion();
}

/* ============ 1. EJERCICIOS GUARDADOS (localStorage) ============ */
function leerEjercicios() {
  try {
    const lista = JSON.parse(localStorage.getItem(CLAVE_EJERCICIOS) || "[]");
    return Array.isArray(lista) ? lista : [];
  } catch (e) {
    return [];
  }
}

function escribirEjercicios(lista) {
  try {
    localStorage.setItem(CLAVE_EJERCICIOS, JSON.stringify(lista));
    return true;
  } catch (e) {
    return false;
  }
}

function guardarEjercicio() {
  if (!matriz.length) {
    mostrarToast("Primero crea un grafo.");
    return;
  }
  const sugerido = `Grafo de ${n} nodos`;
  const entrada = window.prompt("Nombre del ejercicio:", sugerido);
  if (entrada === null) return;
  const nombre = entrada.trim().slice(0, 60) || sugerido;

  const lista = leerEjercicios();
  const previo = lista.findIndex((e) => String(e.nombre).toLowerCase() === nombre.toLowerCase());
  if (previo >= 0 && !window.confirm(`Ya existe «${nombre}». ¿Quieres reemplazarlo?`)) return;

  const registro = {
    id: Date.now().toString(36),
    nombre,
    fecha: new Date().toISOString(),
    n,
    matriz: matriz.map((fila) => fila.slice()),
    etiquetas: etiquetas.slice(),
    posiciones: posiciones ? posiciones.map((p) => p.slice()) : null,
  };
  if (previo >= 0) lista[previo] = registro;
  else lista.push(registro);

  mostrarToast(escribirEjercicios(lista)
    ? `Ejercicio «${nombre}» guardado`
    : "No se pudo guardar: el navegador bloqueó el almacenamiento local.");
}

function renderizarListaGuardados() {
  const ul = $("lista-guardados");
  const lista = leerEjercicios().sort((a, b) => String(b.fecha).localeCompare(String(a.fecha)));
  ul.replaceChildren();
  $("vacio-guardados").classList.toggle("oculto", lista.length > 0);

  lista.forEach((registro) => {
    const fecha = new Date(registro.fecha);
    const meta = `${registro.matriz ? registro.matriz.length : "?"} nodos · ` +
      (Number.isNaN(fecha.getTime()) ? "sin fecha" : fecha.toLocaleString("es", { dateStyle: "medium", timeStyle: "short" }));

    const botonCargar = crearElemento("button", { type: "button", className: "btn btn--primario btn--chico", texto: "Cargar" });
    const botonEliminar = crearElemento("button", { type: "button", className: "btn btn--secundario btn--chico", texto: "Eliminar" });
    botonCargar.addEventListener("click", () => cargarEjercicio(registro.id));
    botonEliminar.addEventListener("click", () => eliminarEjercicio(registro.id));

    ul.appendChild(crearElemento("li", { estilo: "cursor:default" },
      crearElemento("div", { estilo: "min-width:0" },
        crearElemento("strong", { texto: registro.nombre, estilo: "display:block;overflow-wrap:anywhere" }),
        crearElemento("span", { className: "nota", texto: meta, estilo: "margin:0" })),
      crearElemento("div", { estilo: "display:flex;gap:.4rem;flex:none" }, botonCargar, botonEliminar)));
  });
}

function abrirModalGuardados() {
  renderizarListaGuardados();
  abrirModal("modal-guardados");
}

function cargarEjercicio(id) {
  const registro = leerEjercicios().find((e) => e.id === id);
  if (!registro) return;
  try {
    const grafo = normalizarGrafo(registro);
    cerrarModal("modal-guardados");
    aplicarGrafo(grafo);
    mostrarToast(`Ejercicio «${registro.nombre}» cargado`);
  } catch (e) {
    mostrarToast("El ejercicio guardado está dañado: " + e.message);
  }
}

function eliminarEjercicio(id) {
  const lista = leerEjercicios();
  const registro = lista.find((e) => e.id === id);
  if (!registro || !window.confirm(`¿Eliminar «${registro.nombre}»?`)) return;
  escribirEjercicios(lista.filter((e) => e.id !== id));
  renderizarListaGuardados();
}

/* ============ 2. EXPORTACIÓN A PDF ============ */
const celdasDeBloques = (bloques) => {
  const celdas = new Set();
  bloques.forEach(([a, b]) => {
    for (let i = a; i <= b; i++) for (let j = a; j <= b; j++) celdas.add(`${i},${j}`);
  });
  return celdas;
};

const colorPorComponente = (componentes) => {
  const mapa = {};
  componentes.forEach((comp, k) => comp.forEach((nodo) => { mapa[nodo - 1] = PALETA_COMPONENTES[k % PALETA_COMPONENTES.length]; }));
  return (i) => mapa[i];
};

/**
 * Vista "en islas" del resultado: cada componente ocupa su propia celda de una cuadrícula
 * (columnas = ceil(sqrt(k))) y sus nodos se acomodan en círculo dentro de ella.
 * Devuelve:
 *  - posSeparadas:   [x, y] entre 0 y 1 para cada nodo
 *  - matrizSeparada: copia de `matriz` con 0 en las aristas que unen componentes distintas y en la diagonal (sin bucles)
 * `componentes` usa nodos base 1, como en calcularProcedimiento().
 */
function calcularGrafoSeparado(componentes) {
  const k = componentes.length;
  const columnas = Math.ceil(Math.sqrt(k));
  const filas = Math.ceil(k / columnas);
  const anchoCelda = 1 / columnas;
  const altoCelda = 1 / filas;
  const radioAnillo = 0.34 * Math.min(anchoCelda, altoCelda);    // deja margen para los nodos dentro de la celda

  const posSeparadas = new Array(matriz.length);
  const compDe = new Array(matriz.length).fill(0);

  componentes.forEach((componente, idx) => {
    const cx = ((idx % columnas) + 0.5) * anchoCelda;
    const cy = (Math.floor(idx / columnas) + 0.5) * altoCelda;
    const m = componente.length;
    const radio = m > 1 ? radioAnillo : 0;                        // un nodo solo va al centro de su celda

    componente.forEach((nodo, t) => {
      const angulo = (2 * Math.PI * t) / m - Math.PI / 2;         // el primer nodo arriba, como en el círculo original
      posSeparadas[nodo - 1] = [cx + radio * Math.cos(angulo), cy + radio * Math.sin(angulo)];
      compDe[nodo - 1] = idx;
    });
  });

  const matrizSeparada = matriz.map((fila, i) => fila.map((valor, j) => (compDe[i] === compDe[j] ? valor : 0)));
  // Los bucles solo se ven y se editan en la pantalla de edición: en el resultado la diagonal se fuerza a 0
  for (let i = 0; i < matrizSeparada.length; i++) matrizSeparada[i][i] = 0;
  return { posSeparadas, matrizSeparada };
}

/** Imagen (data URL) del grafo para el PDF: componentes separadas, cada una con su color. */
function imagenDelGrafo(componentes) {
  const canvas = document.createElement("canvas");
  const c = prepararLienzo(canvas);
  const { posSeparadas, matrizSeparada } = calcularGrafoSeparado(componentes);
  trazarGrafo(c, matrizSeparada, etiquetas, posSeparadas, { colorNodo: colorPorComponente(componentes) });
  return canvas.toDataURL("image/png");
}

/** Informe completo (todas las etapas + solución) para el PDF, independiente de la etapa visible. */
function construirInforme(proc) {
  const E = etiquetas;
  const etqOrden = proc.orden.map((i) => E[i]);
  const fecha = new Date().toLocaleString("es", { dateStyle: "long", timeStyle: "short" });

  const estilos = crearElemento("style", {}, `
    .informe{font-family:Inter,system-ui,"Segoe UI",Arial,sans-serif;color:#25133E;background:#fff;line-height:1.45}
    .informe h1{font-size:20px;margin:0 0 2px}
    .informe h2{font-size:14px;margin:0 0 3px}
    .informe p{font-size:11.5px;color:#5B4F72;margin:0 0 6px}
    .informe .pdf-bloque{margin:0 0 14px;padding-top:4px}
    .informe .matriz-marco{max-width:calc(var(--cols,5)*34px + 36px)}
    .informe .celda{font-size:11px}
    .informe .celda--bloque{box-shadow:none}
    .informe .res{font-size:13px;margin:0 0 4px;color:#25133E}
  `);

  const seccion = (titulo, descripcion, ...contenido) => crearElemento("div", { className: "pdf-bloque" },
    crearElemento("h2", { texto: titulo }),
    descripcion ? crearElemento("p", { texto: descripcion }) : "",
    ...contenido);

  const textoNuevos = (it) => {
    const lista = it.nuevos.slice(0, 24).map(([i, j, t]) => `${E[i]}→${E[t]}→${E[j]}`).join(", ");
    return it.nuevos.length > 24 ? `${lista} y ${it.nuevos.length - 24} más` : lista;
  };

  const bloquesBorde = crearMatrizDOM(proc.R_final, etqOrden, etqOrden);
  proc.bloques.forEach(([a, b]) => {
    bloquesBorde.querySelectorAll(".celda[data-i]").forEach((celda) => {
      const i = Number(celda.dataset.i);
      const j = Number(celda.dataset.j);
      if (i < a || i > b || j < a || j > b) return;
      const borde = "2px solid #25133E";
      if (i === a) celda.style.borderTop = borde;
      if (i === b) celda.style.borderBottom = borde;
      if (j === a) celda.style.borderLeft = borde;
      if (j === b) celda.style.borderRight = borde;
    });
  });

  const diagonal = new Set();      // solo los 1's agregados: un bucle ya era 1
  E.forEach((_, i) => { if (matriz[i][i] === 0) diagonal.add(`${i},${i}`); });
  const raiz = crearElemento("div", { className: "informe" },
    estilos,
    crearElemento("div", { className: "pdf-bloque" },
      crearElemento("h1", { texto: "Componentes conexas de un grafo dirigido" }),
      crearElemento("p", { texto: `${n} nodos · ${fecha}` })),
    seccion("Matriz de adyacencia", "Un 1 en la posición (i, j) indica una arista de i hacia j.", crearMatrizDOM(matriz, E, E)),
    seccion("Paso 1: matriz con diagonal", "Se agrega el valor 1 en toda la diagonal principal (celdas azules).",
      crearMatrizDOM(proc.M1, E, E, { diagonal })));

  proc.iteraciones.forEach((it) => {
    const nuevos = new Set(it.nuevos.map(([i, j]) => `${i},${j}`));
    raiz.append(seccion(
      `Paso 2: M^${it.exponente} = M^${it.exponente - 1} · M`,
      it.estable
        ? "Al multiplicar otra vez no aparecen 1's nuevos: ya se encontraron todos los caminos."
        : `1's nuevos en naranja (origen→intermedio→destino): ${textoNuevos(it)}.`,
      crearMatrizDOM(it.matriz, E, E, { nuevos })));
  });

  raiz.append(
    seccion("Paso 2: matriz de caminos M_R∞", "Indica qué nodos son alcanzables desde cada nodo.", crearMatrizDOM(proc.R, E, E)),
    seccion("Paso 3: filas ordenadas", "Filas ordenadas por cantidad de 1's (de mayor a menor); en empate, el primer 1 más cercano a la primera columna.",
      crearMatrizDOM(proc.R_filas, etqOrden, E)),
    seccion("Paso 4: columnas ordenadas y bloques", "Los bloques cuadrados diagonales marcados con borde grueso son las componentes conexas.", bloquesBorde),
    seccion("Resultado", `Número total de componentes conexas: ${proc.componentes.length}`,
      ...proc.componentes.map((comp, k) => crearElemento("p", {
        className: "res",
        texto: `V${k + 1} = {${comp.map((nodo) => E[nodo - 1]).join(", ")}}`,
      })),
      crearElemento("img", {
        src: imagenDelGrafo(proc.componentes),
        alt: "Grafo con sus componentes conexas",
        estilo: "display:block;width:320px;height:320px;margin:8px auto 0;border:1px solid #DDE1E8;border-radius:8px",
      })));
  return raiz;
}

async function descargarPDF() {
  if (typeof html2pdf === "undefined") {
    mostrarToast("No se pudo cargar html2pdf. Revisa tu conexión a internet.");
    return;
  }
  const boton = $("btn-pdf");
  const textoOriginal = boton.textContent;
  boton.disabled = true;
  boton.textContent = "Generando PDF…";

  try {
    const informe = construirInforme(calcularProcedimiento(matriz));
    await html2pdf().set({
      margin: [10, 10, 10, 10],
      filename: `informe_componentes_${n}nodos.pdf`,
      image: { type: "jpeg", quality: 0.98 },
      html2canvas: { scale: 2, useCORS: true, backgroundColor: "#ffffff" },
      jsPDF: { unit: "mm", format: "a4", orientation: "portrait" },
      pagebreak: { mode: ["css", "legacy"], avoid: ".pdf-bloque" },
    }).from(informe).save();
    mostrarToast("PDF descargado");
  } catch (e) {
    mostrarToast("No se pudo generar el PDF.");
  } finally {
    boton.disabled = false;
    boton.textContent = textoOriginal;
  }
}

/* ============ 3A. IMPORTAR GRAFO DESDE UNA IMAGEN QR ============ */
function abrirModalImportarQR() {
  $("mensaje-qr").textContent = "";
  $("archivo-qr").value = "";
  abrirModal("modal-qr");
}

async function importarDesdeImagenQR(archivo) {
  const mensaje = $("mensaje-qr");
  if (typeof Html5Qrcode === "undefined") {
    mensaje.textContent = "No se pudo cargar el lector de QR. Revisa tu conexión a internet.";
    return;
  }
  mensaje.textContent = "Leyendo código…";
  const lector = new Html5Qrcode("lector-qr");

  try {
    let texto;
    try {
      texto = await lector.scanFile(archivo, false);
    } catch (e) {
      mensaje.textContent = "No se detectó ningún código QR. Usa una imagen nítida y con borde blanco alrededor del código.";
      return;
    }

    let grafo;
    try {
      grafo = decodificarGrafoDeQR(texto);
    } catch (e) {
      mensaje.textContent = e.message;
      return;
    }

    mensaje.textContent = "";
    cerrarModal("modal-qr");
    aplicarGrafo(grafo);
    mostrarToast("Grafo importado desde el código QR");
  } finally {
    try {
      const r = lector.clear();
      if (r && r.catch) r.catch(() => {});
    } catch (e) { /* nada que limpiar */ }
  }
}

/* ============ 3B. COMPARTIR: GENERAR QR (qrcodejs por CDN, carga diferida) ============ */
function asegurarModalCompartir() {
  if ($("modal-compartir")) return;
  const descargar = crearElemento("button", { type: "button", className: "btn btn--primario", texto: "Descargar QR (.png)" });
  const cerrar = crearElemento("button", { type: "button", className: "btn btn--secundario", texto: "Cerrar" });
  descargar.addEventListener("click", descargarQR);
  cerrar.addEventListener("click", () => cerrarModal("modal-compartir"));

  const modal = crearElemento("div", {
    id: "modal-compartir", className: "modal oculto", role: "dialog", "aria-modal": "true", "aria-labelledby": "t-modal-compartir",
  },
    crearElemento("div", { className: "modal__caja" },
      crearElemento("h3", { id: "t-modal-compartir", className: "card__subtitulo", texto: "Compartir por código QR" }),
      crearElemento("p", { className: "card__texto", texto: "Guarda la imagen y envíasela a un compañero: podrá abrirla con «Cargar QR»." }),
      crearElemento("div", { id: "contenedor-qr", estilo: "display:flex;justify-content:center;margin:1rem 0 .5rem;padding:16px;background:#fff;border:1px solid #DDE1E8;border-radius:12px;min-height:288px;align-items:center" }),
      crearElemento("p", { id: "info-qr", className: "nota", role: "status" }),
      crearElemento("div", { className: "controles" }, descargar, cerrar)));

  modal.addEventListener("click", (e) => { if (e.target === modal) cerrarModal("modal-compartir"); });
  document.body.appendChild(modal);
}

/** Dibuja el QR con corrección M y, si no cabe, con L. Devuelve false si el texto es demasiado largo. */
function dibujarQR(contenedor, texto) {
  for (const nivel of [QRCode.CorrectLevel.M, QRCode.CorrectLevel.L]) {
    contenedor.replaceChildren();
    try {
      new QRCode(contenedor, { text: texto, width: 256, height: 256, colorDark: "#000000", colorLight: "#ffffff", correctLevel: nivel });
      return true;
    } catch (e) { /* probar con menos corrección */ }
  }
  contenedor.replaceChildren();
  return false;
}

async function abrirModalCompartirQR() {
  if (!matriz.length) {
    mostrarToast("Primero crea un grafo.");
    return;
  }
  asegurarModalCompartir();
  const contenedor = $("contenedor-qr");
  const info = $("info-qr");
  contenedor.replaceChildren();
  info.textContent = "Generando código QR…";
  abrirModal("modal-compartir");

  try {
    await cargarScript(URL_QRCODEJS);
  } catch (e) {
    info.textContent = "No se pudo cargar la librería de QR. Revisa tu conexión a internet.";
    return;
  }

  const texto = codificarGrafoParaQR();
  info.textContent = dibujarQR(contenedor, texto)
    ? `Grafo de ${n} nodos codificado en ${texto.length} caracteres.`
    : "El grafo es demasiado grande para un código QR (acorta los nombres de los nodos).";
}

/** Descarga el QR como PNG con un margen blanco, necesario para que otros lectores lo reconozcan. */
function descargarQR() {
  const origen = $("contenedor-qr").querySelector("canvas") || $("contenedor-qr").querySelector("img");
  if (!origen) {
    mostrarToast("Todavía no hay un código QR para descargar.");
    return;
  }
  const margen = 32;
  const lado = origen.width || 256;
  const salida = document.createElement("canvas");
  salida.width = salida.height = lado + 2 * margen;
  const c = salida.getContext("2d");
  c.fillStyle = "#ffffff";
  c.fillRect(0, 0, salida.width, salida.height);
  c.drawImage(origen, margen, margen, lado, lado);

  const enlace = crearElemento("a", { href: salida.toDataURL("image/png"), download: `grafo_${n}nodos_qr.png` });
  document.body.appendChild(enlace);
  enlace.click();
  enlace.remove();
}

/* ============ MANUAL DE USUARIO ============ */
const CONTENIDO_MANUAL = [
  {
    titulo: "1. Inicio rápido",
    html: `
      <h3>¿Para qué sirve esta aplicación?</h3>
      <p>Calcula las componentes conexas de un grafo dirigido con el procedimiento matricial de la clase (matriz de adyacencia, matriz de caminos, orden de filas y columnas, bloques de 1's) y te muestra cada paso.</p>
      <h3>Pasos básicos</h3>
      <ol>
        <li>En la pantalla de inicio elige la cantidad de nodos (de 4 a 12) y presiona <strong>Aleatorio</strong> o <strong>Manual</strong>. También puedes usar <strong>Cargar QR</strong> o <strong>Ejercicios guardados</strong>.</li>
        <li>En la pantalla de edición revisa la matriz y el grafo. Puedes cambiar los 1 y 0 de la matriz o dibujar y quitar flechas sobre el grafo.</li>
        <li>Presiona <strong>Ejecutar algoritmo →</strong> para ver el procedimiento paso a paso.</li>
        <li>Avanza con <strong>Siguiente</strong> hasta la última etapa: la solución, con el número de componentes, los nodos de cada una y el grafo coloreado.</li>
        <li>Presiona <strong>Descargar informe en PDF</strong> para guardar la solución completa.</li>
        <li>Con <strong>Guardar ejercicio</strong> lo conservas para después y, en la pantalla de resultados, con <strong>Compartir QR</strong> se lo envías a otra persona.</li>
      </ol>
      <h3>Las tres etapas</h3>
      <p>La barra de progreso de arriba indica dónde estás: Inicio, Edición o Resultados.</p>`,
  },
  {
    titulo: "2. Pantalla de bienvenida",
    html: `
      <h3>Cantidad de nodos</h3>
      <p>Se elige con los botones − y +, con el deslizador o escribiendo el número. Debe estar entre 4 y 12; si escribes otro valor, se ajusta solo al límite más cercano. Los nodos se numeran 1, 2, 3… (después puedes cambiar sus nombres).</p>
      <h3>Crear nuevo grafo</h3>
      <ul>
        <li><strong>Aleatorio:</strong> el programa crea conexiones al azar entre los nodos.</li>
        <li><strong>Manual:</strong> empiezas con la matriz vacía y tú pones las conexiones.</li>
      </ul>
      <p>Los dos botones abren directamente la pantalla de edición.</p>
      <h3>Cargar grafo existente</h3>
      <ul>
        <li><strong>Cargar QR:</strong> lee una imagen PNG o JPG con el código QR de un ejercicio y lo carga automáticamente.</li>
        <li><strong>Ejercicios guardados:</strong> abre la lista de ejercicios que guardaste antes para cargar uno directamente.</li>
      </ul>
      <h3>Manual de usuario</h3>
      <p>El botón de la esquina superior derecha abre esta ayuda desde cualquier pantalla.</p>`,
  },
  {
    titulo: "3. Pantalla de la matriz",
    html: `
      <h3>La tabla</h3>
      <p>Es la matriz de adyacencia. La <strong>fila es el ORIGEN</strong> y la <strong>columna es el DESTINO</strong>. Un 1 (verde) en la fila A y la columna B significa que hay una flecha de A hacia B. El grafo es dirigido: A→B no significa que exista B→A. La diagonal también se puede editar: un 1 en la fila A y la columna A es un <strong>bucle</strong> (una flecha de A hacia sí mismo).</p>
      <h3>El grafo</h3>
      <p>A la derecha de la matriz se ve el grafo, con todos los nodos del mismo color (así no se adelanta el resultado). Se actualiza solo cada vez que cambias la matriz y respeta la posición que le des a cada nodo.</p>
      <h3>Herramientas del grafo</h3>
      <ul>
        <li><strong>Por defecto (aristas):</strong> arrastra desde el nodo origen hasta el nodo destino. Si la arista no existe se crea y, si ya existe, se quita.</li>
        <li><strong>Mover nodos:</strong> es un interruptor. Al activarlo, arrastras los nodos para acomodarlos; al volver a presionarlo, regresas a las aristas.</li>
      </ul>
      <h3>Botones</h3>
      <ul>
        <li><strong>Aleatorio:</strong> genera otra matriz aleatoria con los mismos nodos, conservando posiciones y nombres.</li>
        <li><strong>Limpiar:</strong> quita todas las conexiones y deja la matriz en ceros.</li>
        <li><strong>Editar arista manual:</strong> agrega o quita una conexión eligiéndola en listas.</li>
        <li><strong>Nombrar nodos:</strong> cambia los nombres de los nodos.</li>
        <li><strong>Guardar ejercicio:</strong> guarda el grafo en tu navegador para abrirlo más tarde.</li>
        <li><strong>← Volver:</strong> regresa a la pantalla de inicio. El grafo actual se reemplaza cuando crees uno nuevo, así que guárdalo antes si quieres conservarlo.</li>
        <li><strong>Ejecutar algoritmo →:</strong> abre el procedimiento paso a paso.</li>
      </ul>
      <h3>Análisis de nodo</h3>
      <p>Debajo de la matriz, elige un nodo en la lista y presiona <strong>Analizar</strong>: muestra a qué nodos llega directamente (por ejemplo A->B, A->C) o "Ninguna" si no tiene salidas.</p>`,
  },
  {
    titulo: "4. Compartir por Código QR",
    html: `
      <h3>Intercambio de ejercicios sin servidor</h3>
      <p>Esta función te permite pasar un ejercicio completo a otra persona como una imagen. El grafo no se envía a ningún servidor: queda dentro del código QR.</p>
      <h3>Generar y enviar un QR</h3>
      <ol>
        <li>Ve a la última etapa del procedimiento (la solución) y presiona <strong>Compartir QR</strong>, junto al botón del informe en PDF.</li>
        <li>En la ventana que aparece, presiona <strong>Descargar QR (.png)</strong> y guarda la imagen.</li>
        <li>Envía la imagen a un compañero por mensaje, correo o red social.</li>
      </ol>
      <h3>Cargar un ejercicio desde un QR</h3>
      <ol>
        <li>En la pantalla de inicio, presiona <strong>Cargar QR</strong>.</li>
        <li>Selecciona la imagen PNG o JPG que te enviaron.</li>
        <li>El programa lee el código y carga la matriz, los nombres de los nodos y sus posiciones, y abre la pantalla de edición.</li>
      </ol>
      <h3>Consejos</h3>
      <p>Usa una imagen nítida y completa, con borde blanco alrededor del código. Si aparece un aviso de que el código no pertenece a la aplicación, revisa que sea el QR de un ejercicio.</p>`,
  },
  {
    titulo: "5. Editar matriz y gráfico",
    html: `
      <p>Hay tres formas de modificar el grafo, y todas se aplican al instante (no hay botón Aceptar ni Cancelar).</p>
      <h3>1. Clic en la matriz</h3>
      <p>Haz clic en cualquier celda para cambiar 0 por 1 o 1 por 0. Las celdas de la diagonal también se pueden editar: crean o quitan un bucle.</p>
      <h3>2. Editar arista manual</h3>
      <p>Elige el <strong>Origen</strong> y el <strong>Destino</strong> en las listas y presiona <strong>Agregar</strong> o <strong>Quitar</strong>. Si la conexión ya existe (o no existe), el programa avisa. Agregar y Quitar no cierran la ventana, así puedes editar varias aristas seguidas; usa <strong>Cerrar</strong> al terminar.</p>
      <p>Si eliges el mismo nodo como origen y destino, agregas o quitas un bucle (una flecha del nodo hacia sí mismo).</p>
      <h3>3. Dibujar sobre el grafo</h3>
      <ul>
        <li><strong>Aristas (modo por defecto):</strong> arrastra con el mouse (o el dedo) desde el nodo origen hasta el nodo destino. La flecha de guía es morada si vas a crear la arista y gris si ya existe y vas a quitarla. Para un bucle, haz clic sobre un nodo (o suéltalo sobre sí mismo): se dibuja un arco que sale y vuelve al nodo.</li>
        <li><strong>Mover nodos:</strong> presiona el botón para activarlo y arrastra un nodo para formar la figura que prefieras; vuelve a presionarlo para regresar a las aristas. Las posiciones se conservan al guardar el ejercicio y al compartirlo por QR.</li>
      </ul>
      <p>Mientras editas, los nodos no cambian de color: las componentes se muestran recién al final.</p>`,
  },
  {
    titulo: "6. Nombrar nodos",
    html: `
      <h3>Un solo estilo para todos</h3>
      <p>Primero eliges UN estilo que se aplica a todos los nodos:</p>
      <ul>
        <li><strong>Números:</strong> del 1 al 999.</li>
        <li><strong>Letras:</strong> mayúsculas o minúsculas (la opción "Letras en" decide cuál; no se pueden mezclar).</li>
        <li><strong>Prefijo + número:</strong> una letra de prefijo igual para todos y un número del 1 al 99 por nodo (por ejemplo Q1, Q2, Q3).</li>
      </ul>
      <h3>Cómo escribir</h3>
      <ul>
        <li>Números: solo acepta dígitos (máximo 3 y sin cero al inicio).</li>
        <li>Letras: solo acepta una letra. Si escribes "v" y está en Mayúsculas, se convierte en "V".</li>
        <li>Prefijo + número: escribes la letra del prefijo (si pones "q" minúscula, todos quedan con q) y el número de cada nodo.</li>
      </ul>
      <h3>Regla de los dígitos</h3>
      <p>Si algún número del prefijo es 10 o más, todos quedan con 2 dígitos para que haya orden: Q01, Q02, …, Q12. Si ninguno llega a 10, quedan Q1, Q2, Q3…</p>
      <h3>Botones</h3>
      <ul>
        <li><strong>Por defecto:</strong> deja nombres consecutivos (A, B, C… / 1, 2, 3… / Q1, Q2…).</li>
        <li><strong>Rellenar:</strong> completa los demás nodos a partir del primero (si el primero es 10 quedan 10, 11, 12…; si es "c" quedan c, d, e…). Si ya no alcanzan los valores (por ejemplo empezando en Z), avisa.</li>
        <li><strong>Aceptar:</strong> valida que no haya campos vacíos ni nombres repetidos y aplica los nombres.</li>
        <li><strong>Cancelar:</strong> cierra sin cambiar nada.</li>
      </ul>
      <p>Los nombres se usan en todo el programa: matriz, análisis, gráficos, pasos, resultado e informe.</p>`,
  },
  {
    titulo: "7. Graficar componentes conexas",
    html: `
      <p>El grafo original se ve siempre junto a la matriz. El resultado final aparece en la <strong>última etapa</strong> del procedimiento (la solución): el grafo de las componentes conexas.</p>
      <p>Cada componente aparece separada de las demás, en su propio espacio de una cuadrícula y con su propio color. Dentro de cada una los nodos se acomodan en círculo, y solo se dibujan las flechas que están dentro de la componente; las flechas entre componentes distintas y los bucles no se muestran.</p>
      <p>Esta vista se reorganiza sola, así que las posiciones que diste a los nodos solo afectan al grafo original. A su lado se lista cada componente con sus nodos (V1, V2, …).</p>`,
  },
  {
    titulo: "8. Procedimiento paso a paso",
    html: `
      <p>Se abre con <strong>Ejecutar algoritmo →</strong>. Muestra cómo cambia la matriz en cada etapa; arriba se indica "Etapa X de Y" con una barra de progreso.</p>
      <h3>Etapas</h3>
      <ol>
        <li><strong>Paso 1:</strong> matriz de adyacencia con 1's en la diagonal (los 1's agregados se ven en azul).</li>
        <li><strong>Paso 2:</strong> se multiplica la matriz por sí misma (producto booleano) y se obtiene M², luego M³, y así hasta que ya no aparezcan 1's nuevos. Los 1's nuevos salen en naranja y debajo se explica por qué nodo se pasa (por ejemplo 4→2 (por 1)).</li>
        <li><strong>Matriz de caminos:</strong> es el resultado del Paso 2, con la lista de nodos a los que llega cada nodo.</li>
        <li><strong>Paso 3:</strong> se ordenan las filas por la cantidad de 1's, de mayor a menor. Si hay empate, va primero la fila cuyo primer 1 está más cerca de la primera columna.</li>
        <li><strong>Paso 4:</strong> se ordenan las columnas igual que las filas. Los bloques cuadrados de 1's marcados con borde morado oscuro son las componentes conexas.</li>
        <li><strong>Resultado:</strong> el número de componentes, la lista de nodos de cada una y el grafo coloreado.</li>
      </ol>
      <h3>Botones</h3>
      <ul>
        <li><strong>Anterior / Siguiente:</strong> retroceder o avanzar una etapa.</li>
        <li><strong>Reproducir:</strong> avanza sola de etapa en etapa y se detiene en el resultado. Se convierte en Pausar. Si la presionas al final, vuelve a empezar.</li>
        <li><strong>Velocidad:</strong> Lenta, Normal o Rápida.</li>
        <li><strong>← Volver a Edición:</strong> regresa a corregir el grafo sin perder tus datos.</li>
      </ul>
      <p>Si usas Anterior o Siguiente mientras se reproduce, la reproducción se pausa.</p>
      <h3>Colores</h3>
      <p>Verde = 1, blanco = 0, naranja = 1 nuevo, azul = 1 agregado en la diagonal, borde morado oscuro = bloque de una componente.</p>`,
  },
  {
    titulo: "9. Informe en PDF",
    html: `
      <p>En la pantalla del resultado, el botón <strong>Descargar informe en PDF</strong> arma el informe completo y lo descarga en formato A4 con el nombre <em>informe_componentes_(n)nodos.pdf</em>. El informe incluye siempre todas las etapas, sin importar cuál estés viendo.</p>
      <h3>Contenido del informe</h3>
      <ol>
        <li>Título, cantidad de nodos y fecha.</li>
        <li>La matriz de adyacencia.</li>
        <li>Paso 1: la matriz con la diagonal de 1's.</li>
        <li>Paso 2: cada potencia (M², M³…) con sus 1's nuevos y la matriz de caminos.</li>
        <li>Paso 3: las filas ordenadas.</li>
        <li>Paso 4: las columnas ordenadas con los bloques marcados.</li>
        <li>Resultado: el número de componentes conexas, la lista de nodos de cada una y el grafo coloreado.</li>
      </ol>
      <h3>Si no se descarga</h3>
      <p>Revisa tu conexión a internet (la herramienta que arma el PDF se carga desde la web) y que el navegador no esté bloqueando descargas.</p>`,
  },
  {
    titulo: "10. Ejercicios guardados",
    html: `
      <h3>Guardar</h3>
      <p><strong>Guardar ejercicio</strong> te pide un nombre y guarda el grafo (la matriz, los nombres y la posición de los nodos). Si ya existe un ejercicio con ese nombre, pregunta si quieres reemplazarlo.</p>
      <p>Los ejercicios se guardan en tu navegador, en este dispositivo. No viajan a otros dispositivos ni a otros navegadores, y se pierden si borras los datos del sitio.</p>
      <h3>Ver, cargar y eliminar</h3>
      <p><strong>Ejercicios guardados</strong> (en la pantalla de inicio) muestra la lista con nombre, cantidad de nodos y fecha, del más nuevo al más antiguo.</p>
      <ul>
        <li><strong>Cargar:</strong> abre el ejercicio en la pantalla de edición (reemplaza el grafo actual).</li>
        <li><strong>Eliminar:</strong> lo borra de la lista, después de pedir confirmación.</li>
      </ul>
      <h3>Pasar un ejercicio a otro dispositivo</h3>
      <p>Usa <strong>Compartir QR</strong> y envía la imagen; la otra persona la abre con <strong>Cargar QR</strong>.</p>`,
  },
  {
    titulo: "11. Conceptos del tema",
    html: `
      <h3>Grafo dirigido</h3>
      <p>Es un conjunto de nodos unidos por flechas. Cada flecha va de un nodo origen a un nodo destino.</p>
      <h3>Grafo conexo</h3>
      <p>Un grafo es conexo si para cualquier par de vértices existe un camino entre ellos.</p>
      <h3>Componentes conexas</h3>
      <p>Son los subgrafos conexos disjuntos (sin vértices en común) con el mayor número de vértices que se pueden formar a partir del grafo original.</p>
      <h3>Matriz de adyacencia</h3>
      <p>Tiene un 1 en la fila i y la columna j si existe la arista de i hacia j, y 0 si no existe.</p>
      <h3>Matriz de caminos</h3>
      <p>Indica si desde un nodo se puede llegar a otro siguiendo las flechas, sin importar cuántos pasos tome. Se obtiene multiplicando la matriz de adyacencia por sí misma hasta que ya no cambia.</p>
      <h3>¿Por qué se pone 1 en la diagonal?</h3>
      <p>Porque todo nodo llega a sí mismo. Además, así cada potencia incluye los caminos más cortos y la matriz crece ordenadamente hasta estabilizarse.</p>
      <h3>¿Cómo se forman las componentes?</h3>
      <p>Dos nodos están en la misma componente si se alcanzan mutuamente (de uno al otro y de vuelta). Al ordenar filas y columnas, esos nodos forman bloques cuadrados diagonales de 1's.</p>`,
  },
  {
    titulo: "12. Preguntas frecuentes",
    html: `
      <h3>Edité con «Editar arista manual» pero no cambió nada</h3>
      <p>Esa ventana aplica los cambios al presionar <strong>Agregar</strong> o <strong>Quitar</strong>; cerrarla sin presionarlos no modifica nada.</p>
      <h3>No me deja guardar los nombres de los nodos</h3>
      <p>Revisa que no haya campos vacíos ni nombres repetidos. Los nombres tienen como máximo 3 caracteres.</p>
      <h3>¿Dónde quedan mis ejercicios?</h3>
      <p>En el almacenamiento de tu navegador, en este dispositivo. Se ven en el botón <strong>Ejercicios guardados</strong>.</p>
      <h3>¿Cómo transfiero mi ejercicio a un amigo?</h3>
      <p>Usa <strong>Compartir QR</strong>, guarda la imagen con <strong>Descargar QR (.png)</strong> y envíasela. Tu amigo solo debe presionar <strong>Cargar QR</strong> en su aplicación.</p>
      <h3>El QR no se lee</h3>
      <p>Usa una imagen nítida y completa, con borde blanco alrededor del código.</p>
      <h3>No se genera el QR, no se lee o no se descarga el PDF</h3>
      <p>Esas funciones usan herramientas que se cargan desde internet al abrir la página. Revisa tu conexión y recarga la página.</p>
      <h3>¿Puedo conectar un nodo consigo mismo?</h3>
      <p>Sí, eso es un bucle. Se crea con un 1 en la diagonal de la matriz, haciendo clic sobre el nodo en el grafo, o con «Editar arista manual» eligiendo el mismo nodo de origen y destino. Los bucles no cambian las componentes (en el procedimiento se agrega un 1 en la diagonal de todos modos), por eso no se dibujan en la solución.</p>`,
  },
];

function construirListaManual() {
  $("lista-manual").replaceChildren(...CONTENIDO_MANUAL.map((tema, i) => {
    const boton = crearElemento("button", { type: "button", className: "manual__tema", texto: tema.titulo });
    boton.addEventListener("click", () => mostrarTemaManual(i));
    return boton;
  }));
}

/** Muestra un tema en #contenido-manual y marca el tema activo de la lista. */
function mostrarTemaManual(indice) {
  const tema = CONTENIDO_MANUAL[indice];
  if (!tema) return;
  const contenido = $("contenido-manual");
  contenido.innerHTML = `<h2>${tema.titulo}</h2>${tema.html}`;     // contenido propio y fijo (no viene del usuario)
  contenido.scrollTop = 0;
  [...$("lista-manual").children].forEach((boton, i) => boton.setAttribute("aria-current", String(i === indice)));
}

/** Abre el manual siempre en el primer tema. */
function abrirModalManual() {
  construirListaManual();
  mostrarTemaManual(0);
  abrirModal("modal-manual");
  $("lista-manual").children[0].focus();
}

/* ============ CONEXIÓN DE EVENTOS ============ */
function inicializarAvanzadas() {
  // El modal de QR solo admite imagen (no cámara): se ajusta el texto del HTML
  const aviso = document.querySelector("#modal-qr .card__texto");
  if (aviso) aviso.textContent = "Sube una imagen con el código QR de un grafo exportado desde esta aplicación.";

  // Ejercicios guardados
  $("btn-guardar").addEventListener("click", guardarEjercicio);
  $("btn-guardados").addEventListener("click", abrirModalGuardados);
  $("btn-cerrar-guardados").addEventListener("click", () => cerrarModal("modal-guardados"));

  // Importar QR
  $("btn-qr").addEventListener("click", abrirModalImportarQR);
  $("btn-cerrar-qr").addEventListener("click", () => cerrarModal("modal-qr"));
  $("archivo-qr").addEventListener("change", (e) => {
    const archivo = e.target.files[0];
    if (archivo) importarDesdeImagenQR(archivo);
    e.target.value = "";
  });

  // Compartir QR (botón de la pantalla de resultados)
  $("btn-compartir-qr").addEventListener("click", abrirModalCompartirQR);

  // PDF
  $("btn-pdf").addEventListener("click", descargarPDF);

  // Manual de usuario
  $("btn-manual-uso").addEventListener("click", abrirModalManual);
  $("btn-cerrar-manual").addEventListener("click", () => cerrarModal("modal-manual"));

  // Modal de confirmación
  $("btn-confirmar-aceptar").addEventListener("click", aceptarConfirmacion);
  $("btn-confirmar-cancelar").addEventListener("click", cancelarConfirmacion);
  $("modal-confirmacion").addEventListener("click", (e) => { if (e.target === $("modal-confirmacion")) cancelarConfirmacion(); });

  // Cierre de modales: clic en el fondo y tecla Escape
  ["modal-qr", "modal-guardados", "modal-manual"].forEach((id) => {
    $(id).addEventListener("click", (e) => { if (e.target === $(id)) cerrarModal(id); });
  });
  document.addEventListener("keydown", (e) => {
    if (e.key !== "Escape") return;
    const abierto = IDS_MODALES.find((id) => $(id) && !$(id).classList.contains("oculto"));
    if (abierto) cerrarModal(abierto);
  });
}

inicializarAvanzadas();


/* ==========================================================================
   VISIÓN ARTIFICIAL · escanear una imagen con Gemini (Modo Profesional)
   La API Key la pone el usuario y vive solo en su localStorage (no hay backend).
   ========================================================================== */

const CLAVE_API_GEMINI = "gemini_api_key";
// gemini-1.5-flash ya no existe en la API (Google lo apagó el 29-sep-2025). Si este modelo se retira, cambia solo esta línea.
const MODELO_GEMINI = "gemini-3.8-flash";
const urlGemini = (clave) =>
  `https://generativelanguage.googleapis.com/v1beta/models/${MODELO_GEMINI}:generateContent?key=${encodeURIComponent(clave)}`;
const TAMANO_MAX_IMAGEN_IA = 10 * 1024 * 1024;   // 10 MB (la petición completa admite ~20 MB y Base64 pesa un tercio más)
const TIEMPO_MAX_IA_MS = 60000;
const TEXTO_BTN_IA = $("btn-ia-imagen").querySelector(".opcion__titulo").textContent;

const PROMPT_IA = `Eres un experto en Teoría de Grafos. Analiza esta imagen (puede ser un grafo dirigido dibujado o una matriz) y extrae sus datos. REGLA ESTRICTA: GrafoLab solo soporta entre 4 y 12 nodos. Si detectas menos de 4 o más de 12 nodos, devuelve EXACTAMENTE: {"error": "El grafo debe tener entre 4 y 12 nodos"}. Si cumple, devuelve EXACTAMENTE: {"error": null, "matriz": [[0,1...],...], "coordenadas": [{"x": 0.2, "y": 0.8}, ...]}. Las coordenadas 'x' e 'y' deben ser decimales entre 0.1 y 0.9. Si la imagen es una matriz, inventa coordenadas circulares. NO devuelvas texto, markdown, ni explicaciones, SOLO EL JSON VÁLIDO.`;

let abrirSelectorTrasGuardar = false;   // true si el modal de la clave se abrió desde «Escanear imagen con IA»

/* ---------- Avisos y estado del botón ---------- */
/** Aviso en modal propio (sustituye a window.alert). */
function mostrarAviso(titulo, mensaje) {
  $("t-modal-aviso").textContent = titulo;
  $("texto-aviso").textContent = mensaje;
  abrirModal("modal-aviso");
}

function establecerCargandoIA(cargando) {
  const boton = $("btn-ia-imagen");
  boton.querySelector(".opcion__titulo").textContent = cargando ? "Analizando imagen..." : TEXTO_BTN_IA;
  boton.disabled = cargando;
  boton.setAttribute("aria-busy", String(cargando));
}

/* ---------- API Key ---------- */
function leerApiKey() {
  try { return (localStorage.getItem(CLAVE_API_GEMINI) || "").trim(); } catch (e) { return ""; }
}

function mostrarErrorApiKey(texto) {
  const error = $("error-api-key");
  error.textContent = texto;
  error.classList.toggle("oculto", !texto);
}

function abrirModalApiKey(continuarConEscaneo = false) {
  abrirSelectorTrasGuardar = continuarConEscaneo;
  $("input-api-key").value = "";
  mostrarErrorApiKey("");
  abrirModal("modal-api-key");
}

function cerrarModalApiKey() {
  abrirSelectorTrasGuardar = false;
  $("input-api-key").value = "";
  cerrarModal("modal-api-key");
}

function guardarApiKey() {
  const valor = $("input-api-key").value.trim();
  if (!valor) {
    mostrarErrorApiKey("Escribe tu clave de Gemini para continuar.");
    return;
  }
  try {
    localStorage.setItem(CLAVE_API_GEMINI, valor);
  } catch (e) {
    mostrarErrorApiKey("El navegador bloqueó el almacenamiento local: no se pudo guardar la clave.");
    return;
  }
  const continuar = abrirSelectorTrasGuardar;
  cerrarModalApiKey();
  mostrarToast("API Key guardada");
  if (continuar) $("input-imagen-ia").click();      // venía de «Escanear imagen con IA»: sigue con la imagen
}

/* ---------- Flujo de escaneo ---------- */
function alPulsarEscanearIA() {
  if (!leerApiKey()) {
    abrirModalApiKey(true);
    return;
  }
  $("input-imagen-ia").click();
}

function alElegirImagenIA(e) {
  const archivo = e.target.files[0];
  e.target.value = "";                               // permite elegir de nuevo el mismo archivo
  if (!archivo) return;
  if (!/^image\/(jpeg|png)$/.test(archivo.type)) {
    mostrarAviso("Formato no compatible", "Sube una imagen JPG o PNG.");
    return;
  }
  if (archivo.size > TAMANO_MAX_IMAGEN_IA) {
    mostrarAviso("Imagen demasiado grande", "La imagen pesa más de 10 MB. Reduce su tamaño e inténtalo de nuevo.");
    return;
  }

  establecerCargandoIA(true);
  const lector = new FileReader();
  lector.onload = () => procesarImagenConIA(String(lector.result));
  lector.onerror = () => {
    establecerCargandoIA(false);
    mostrarAviso("No se pudo leer la imagen", "El navegador no pudo leer el archivo. Prueba con otra imagen.");
  };
  lector.readAsDataURL(archivo);
}

/* ---------- Conexión con Gemini ---------- */
function mensajeErrorGemini(estado, detalle) {
  if (estado === 400 && /api key/i.test(detalle)) return "La API Key no es válida. Revísala en «Configurar API Key».";
  if (estado === 400) return `Gemini rechazó la solicitud: ${detalle}`;
  if (estado === 401 || estado === 403) return "Gemini no autorizó la clave. Revisa que sea correcta y que tenga permiso para usar la API (puedes cambiarla en «Configurar API Key»).";
  if (estado === 404) return `El modelo «${MODELO_GEMINI}» ya no está disponible en Gemini. Actualiza MODELO_GEMINI en app.js.`;
  if (estado === 429) return "Se alcanzó el límite de uso de tu clave de Gemini. Espera un momento e inténtalo de nuevo.";
  if (estado >= 500) return "Los servidores de Gemini no respondieron bien. Inténtalo de nuevo en un momento.";
  return `Gemini devolvió el error ${estado}: ${detalle}`;
}

/** Convierte el texto de la IA en un grafo normalizado ({ n, matriz, etiquetas, posiciones }) o lanza Error legible. */
function interpretarRespuestaIA(texto) {
  const invalido = "La IA no devolvió un resultado válido. Prueba con una imagen más clara.";
  const limpio = texto.trim().replace(/^```(?:json)?\s*/i, "").replace(/\s*```$/, "");   // por si envuelve el JSON en Markdown
  const ini = limpio.indexOf("{");
  const fin = limpio.lastIndexOf("}");
  if (ini < 0 || fin <= ini) throw new Error(invalido);

  let json;
  try { json = JSON.parse(limpio.slice(ini, fin + 1)); } catch (e) { throw new Error(invalido); }
  if (json.error) throw new Error(String(json.error));

  const M = json.matriz;
  if (!Array.isArray(M) || !M.every(Array.isArray)) throw new Error("La IA no encontró una matriz de adyacencia en la imagen.");
  const matrizIA = M.map((fila) => fila.map((v) => (Number(v) > 0 ? 1 : 0)));

  // Coordenadas fraccionarias [0, 1]: es el mismo formato de `posiciones` (el lienzo las multiplica por LADO al dibujar)
  const coords = Array.isArray(json.coordenadas) ? json.coordenadas : [];
  let posiciones = coords.length === matrizIA.length && coords.every((c) => c && Number.isFinite(parseFloat(c.x)) && Number.isFinite(parseFloat(c.y)))
    ? coords.map((c) => [parseFloat(c.x), parseFloat(c.y)])
    : null;
  // Si dos nodos quedarían encimados, es mejor el círculo por defecto
  if (posiciones && posiciones.some((p, i) => posiciones.some((q, j) => j > i && Math.hypot(p[0] - q[0], p[1] - q[1]) < 0.07))) posiciones = null;

  return normalizarGrafo({ matriz: matrizIA, posiciones });   // valida 4–12 nodos, matriz cuadrada y 0/1; sin posiciones usa el círculo
}

/** Recibe la imagen como data URL Base64, la analiza con Gemini y abre el grafo en la pantalla de edición. */
async function procesarImagenConIA(base64) {
  const controlador = new AbortController();
  const temporizador = setTimeout(() => controlador.abort(), TIEMPO_MAX_IA_MS);
  try {
    const apiKey = leerApiKey();
    if (!apiKey) throw new Error("No hay una API Key guardada. Configúrala en «Configurar API Key» e inténtalo de nuevo.");

    const prefijo = /^data:(image\/[\w.+-]+);base64,/i.exec(base64);
    const mimeType = prefijo ? prefijo[1] : "image/jpeg";
    const datos = prefijo ? base64.slice(prefijo[0].length) : base64;

    let respuesta;
    try {
      respuesta = await fetch(urlGemini(apiKey), {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        signal: controlador.signal,
        body: JSON.stringify({
          contents: [{ parts: [{ inlineData: { mimeType, data: datos } }, { text: PROMPT_IA }] }],
          generationConfig: { responseMimeType: "application/json" },
        }),
      });
    } catch (e) {
      throw new Error(e.name === "AbortError"
        ? "Gemini tardó demasiado en responder. Inténtalo de nuevo."
        : "No se pudo conectar con Gemini. Revisa tu conexión a internet.");
    }

    if (!respuesta.ok) {
      let detalle = respuesta.statusText;
      try { detalle = (await respuesta.json()).error.message || detalle; } catch (e) { /* sin cuerpo JSON */ }
      throw new Error(mensajeErrorGemini(respuesta.status, detalle));
    }

    const cuerpo = await respuesta.json();
    const partes = (cuerpo.candidates && cuerpo.candidates[0] && cuerpo.candidates[0].content && cuerpo.candidates[0].content.parts) || [];
    const texto = partes.filter((p) => p.text && !p.thought).map((p) => p.text).join("");
    if (!texto.trim()) {
      throw new Error(cuerpo.promptFeedback && cuerpo.promptFeedback.blockReason
        ? "Gemini bloqueó la imagen por sus filtros de seguridad."
        : "Gemini no devolvió ninguna respuesta. Prueba con otra imagen.");
    }

    const grafo = interpretarRespuestaIA(texto);
    if ($("pantalla-inicio").classList.contains("oculto")) {      // el usuario ya salió de la Pantalla 1: no se pisa su trabajo
      mostrarToast("Se descartó el resultado de la IA porque ya saliste de la pantalla de inicio.");
      return;
    }
    aplicarGrafo(grafo);                                          // sobrescribe n, matriz, etiquetas y posiciones y abre la edición
    mostrarToast(`Grafo de ${grafo.n} nodos importado desde la imagen`);
  } catch (e) {
    mostrarAviso("No se pudo analizar la imagen", e.message || "Ocurrió un error inesperado.");
  } finally {
    clearTimeout(temporizador);
    establecerCargandoIA(false);
  }
}

function inicializarVisionIA() {
  $("btn-ia-imagen").addEventListener("click", alPulsarEscanearIA);
  $("input-imagen-ia").addEventListener("change", alElegirImagenIA);
  $("btn-config-ia").addEventListener("click", () => abrirModalApiKey(false));
  $("btn-api-guardar").addEventListener("click", guardarApiKey);
  $("btn-api-cancelar").addEventListener("click", cerrarModalApiKey);
  $("input-api-key").addEventListener("keydown", (e) => { if (e.key === "Enter") guardarApiKey(); });
  $("btn-aviso-cerrar").addEventListener("click", () => cerrarModal("modal-aviso"));
  ["modal-api-key", "modal-aviso"].forEach((id) => {
    $(id).addEventListener("click", (e) => { if (e.target === $(id)) cerrarModal(id); });
  });
}

inicializarVisionIA();


/* ==========================================================================
   PANTALLA 3 · pasos y solución (renderizador visual)
   ========================================================================== */

let vistasPantalla3 = [];      // una entrada por etapa: { tipo, titulo, descripcion, extra, tabla }
let vistaActual = 0;
let reproduciendo = false;
let temporizadorPasos = null;
const ctxResultado = prepararLienzo($("lienzo-resultado"));

/* ---------- Textos de apoyo (mismos que la versión Python) ---------- */
function textoNuevos(E, it) {
  if (it.estable) {
    return `M^${it.exponente} es igual a M^${it.exponente - 1}: ya no aparecen 1's nuevos, ` +
      `así que la matriz de caminos es M^${it.exponente - 1}.`;
  }
  const maximo = 12;
  const partes = it.nuevos.slice(0, maximo).map(([i, j, t]) => `${E[i]}→${E[j]} (por ${E[t]})`);
  let texto = "1's nuevos (naranja): " + partes.join(", ");
  if (it.nuevos.length > maximo) texto += ` ... (y ${it.nuevos.length - maximo} más)`;
  return texto;
}

function textoAlcance(R, E) {
  const lineas = R.map((fila, i) => {
    const alcanzables = E.filter((_, j) => fila[j] === 1);
    return `${E[i]} llega hasta: ${alcanzables.join(", ")}`;
  });
  return "Nodos alcanzables desde cada nodo:\n" + lineas.join("\n");
}

function textoCantidades(R, orden, E) {
  const cantidades = orden.map((i) => `${E[i]} tiene ${R[i].reduce((a, v) => a + v, 0)}`);
  return "Cantidad de 1's por fila (en el orden mostrado):\n" + cantidades.join(", ");
}

/* ---------- 1. Array de vistas ---------- */
/** Convierte el objeto `procedimiento` en la lista de etapas: Paso 1, potencias, caminos, filas, columnas y solución. */
function construirVistasPantalla3(proc) {
  const E = etiquetas;
  const etqOrden = proc.orden.map((i) => E[i]);

  const diagonal = new Set();
  E.forEach((_, i) => { if (matriz[i][i] === 0) diagonal.add(`${i},${i}`); });

  const vistas = [{
    tipo: "paso1",
    titulo: "Paso 1: Matriz de adyacencia + diagonal",
    descripcion: "Se construye la matriz de adyacencia del grafo y se agrega el valor 1 en toda la diagonal principal.",
    extra: diagonal.size > 0 ? "Los 1's agregados en la diagonal se muestran en azul." : "",
    tabla: { M: proc.M1, filas: E, cols: E, opciones: { diagonal } },
  }];

  proc.iteraciones.forEach((it) => {
    const k = it.exponente;
    vistas.push({
      tipo: "potencia",
      titulo: `Paso 2: calculando M^${k} = M^${k - 1} · M`,
      descripcion: it.estable
        ? "Se multiplica otra vez la matriz anterior por M (producto booleano) y el resultado no cambia: ya se encontraron todos los caminos."
        : "Se multiplica (producto booleano) la matriz anterior por la matriz M del Paso 1: hay un 1 en la posición (i, j) " +
          `si i llega a algún nodo t y desde t hay una arista hacia j. Como la diagonal tiene 1's, M^${k} incluye los caminos de hasta ${k} pasos. ` +
          "Los 1's nuevos se marcan en naranja.",
      extra: textoNuevos(E, it),
      tabla: { M: it.matriz, filas: E, cols: E, opciones: { nuevos: new Set(it.nuevos.map(([i, j]) => `${i},${j}`)) } },
    });
  });

  vistas.push({
    tipo: "caminos",
    titulo: "Paso 2: Matriz de caminos (resultado)",
    descripcion: "Cuando al multiplicar ya no aparecen 1's nuevos se obtiene la matriz de caminos M_R∞: indica qué nodos son alcanzables desde cada nodo.",
    extra: textoAlcance(proc.R, E),
    tabla: { M: proc.R, filas: E, cols: E, opciones: {} },
  });

  vistas.push({
    tipo: "filas",
    titulo: "Paso 3: Ordenar filas",
    descripcion: "Se ordenan las filas según la cantidad de 1's que contienen (de mayor a menor). En caso de empate, se prioriza la fila cuyo primer 1 esté más cerca de la primera columna.",
    extra: textoCantidades(proc.R, proc.orden, E),
    tabla: { M: proc.R_filas, filas: etqOrden, cols: E, opciones: {} },
  });

  vistas.push({
    tipo: "columnas",
    titulo: "Paso 4: Ordenar columnas y formar bloques",
    descripcion: "Se reordenan las columnas en el mismo orden que las filas. Los bloques cuadrados diagonales formados por 1's, marcados con borde grueso morado oscuro, son las componentes conexas.",
    extra: "",
    tabla: { M: proc.R_final, filas: etqOrden, cols: etqOrden, opciones: { bloques: celdasDeBloques(proc.bloques) } },
  });

  vistas.push({
    tipo: "resultado",
    titulo: "Resultado: Componentes conexas",
    descripcion: "",
    extra: "",
    tabla: null,
  });

  return vistas;
}

/* ---------- 2. Renderizado de la etapa actual ---------- */
function mostrarSolucion() {
  const proc = procedimiento;
  const colorDe = colorPorComponente(proc.componentes);
  const k = proc.componentes.length;

  $("resumen-total").textContent = `Número total de componentes conexas: ${k}`;
  $("lista-componentes").replaceChildren(...proc.componentes.map((comp, idx) => crearElemento("li", { className: "componente" },
    crearElemento("span", {
      "aria-hidden": "true",
      estilo: `width:14px;height:14px;border-radius:50%;flex:none;border:2px solid #25133E;background:${PALETA_COMPONENTES[idx % PALETA_COMPONENTES.length]}`,
    }),
    crearElemento("span", { className: "componente__nombre", texto: `V${idx + 1}` }),
    crearElemento("span", { className: "componente__nodos", texto: `{${comp.map((nodo) => etiquetas[nodo - 1]).join(", ")}}` }),
    crearElemento("span", { className: "nota", estilo: "margin:0 0 0 auto;min-height:0", texto: `${comp.length} ${comp.length === 1 ? "nodo" : "nodos"}` }))));

  // Componentes separadas en una cuadrícula y sin las aristas que unen componentes distintas
  const { posSeparadas, matrizSeparada } = calcularGrafoSeparado(proc.componentes);
  trazarGrafo(ctxResultado, matrizSeparada, etiquetas, posSeparadas, { colorNodo: colorDe });
}

function mostrarVistaActual(indice = vistaActual) {
  const total = vistasPantalla3.length;
  vistaActual = Math.min(Math.max(indice, 0), total - 1);
  const vista = vistasPantalla3[vistaActual];

  $("etapa-contador").textContent = `Etapa ${vistaActual + 1} de ${total}`;
  $("barra-etapas").style.width = `${((vistaActual + 1) / total) * 100}%`;
  $("btn-anterior").disabled = vistaActual === 0;
  $("btn-siguiente").disabled = vistaActual === total - 1;

  const esSolucion = vista.tipo === "resultado";
  $("zona-pasos").classList.toggle("oculto", esSolucion);
  $("panel-resultado").classList.toggle("oculto", !esSolucion);

  if (esSolucion) {
    mostrarSolucion();
    return;
  }

  $("paso-titulo").textContent = vista.titulo;
  $("paso-descripcion").textContent = vista.descripcion;
  $("paso-extra").textContent = vista.extra;
  const { M, filas, cols, opciones } = vista.tabla;
  $("paso-matriz").replaceChildren(crearMatrizDOM(M, filas, cols, opciones));
}

/** Calcula el procedimiento (si hace falta), arma las vistas y muestra la primera etapa. */
function iniciarPasos() {
  detenerReproduccion();
  if (!procedimiento) procedimiento = calcularProcedimiento(matriz);
  vistasPantalla3 = construirVistasPantalla3(procedimiento);
  mostrarVistaActual(0);
}

/* ---------- 3. Botones: anterior, siguiente y reproducción automática ---------- */
function irAnterior() {
  detenerReproduccion();
  mostrarVistaActual(vistaActual - 1);
}

function irSiguiente() {
  detenerReproduccion();
  mostrarVistaActual(vistaActual + 1);
}

function detenerReproduccion() {
  reproduciendo = false;
  clearTimeout(temporizadorPasos);
  temporizadorPasos = null;
  $("btn-reproducir").textContent = "Reproducir";
}

function programarSiguiente() {
  temporizadorPasos = setTimeout(avanzarAutomatico, Number($("select-velocidad").value));
}

function avanzarAutomatico() {
  if (!reproduciendo) return;
  if (vistaActual < vistasPantalla3.length - 1) mostrarVistaActual(vistaActual + 1);
  if (vistaActual < vistasPantalla3.length - 1) programarSiguiente();
  else detenerReproduccion();
}

function alternarReproduccion() {
  if (reproduciendo) {
    detenerReproduccion();
    return;
  }
  if (vistaActual === vistasPantalla3.length - 1) mostrarVistaActual(0);   // al final: reinicia desde el Paso 1
  reproduciendo = true;
  $("btn-reproducir").textContent = "Pausar";
  programarSiguiente();
}

function inicializarPasos() {
  $("paso-extra").style.whiteSpace = "pre-line";     // respeta los saltos de línea del texto de alcance
  $("btn-anterior").addEventListener("click", irAnterior);
  $("btn-siguiente").addEventListener("click", irSiguiente);
  $("btn-reproducir").addEventListener("click", alternarReproduccion);
  ["btn-volver-edicion", "btn-volver-edicion-resultado"].forEach((id) => $(id).addEventListener("click", mostrarPantallaEdicion));
}

inicializarPasos();


/* ==========================================================================
   NOMBRAR NODOS · modal para elegir un estilo de nombres para todos los nodos
   Estilos: Números (1–999), Letras (A–Z / a–z) y Prefijo + número (Q1…Q99).
   ========================================================================== */

IDS_MODALES.push("modal-nombres");     // para que Escape también cierre este modal

/* ============ NOMBRES_LOGICA_INICIO · funciones puras (sin DOM) ============ */
const ultimaLetra = (texto) => (texto.match(/[A-Za-z]/g) || []).pop() || "";
const soloDigitos = (texto, maximo) => texto.replace(/\D/g, "").replace(/^0+/, "").slice(0, maximo);

/** Deja en un campo solo lo permitido por el estilo: una letra, o dígitos sin ceros a la izquierda. */
function filtrarValorNodo(texto, estilo, mayusculas) {
  if (estilo === "letras") {
    const letra = ultimaLetra(texto);
    return mayusculas ? letra.toUpperCase() : letra.toLowerCase();
  }
  return soloDigitos(texto, estilo === "numeros" ? 3 : 2);
}

/** Valor consecutivo por posición: A, B, C… / a, b, c… / 1, 2, 3… */
function valorPorDefectoNodo(posicion, estilo, mayusculas) {
  if (estilo === "letras") return String.fromCharCode((mayusculas ? 65 : 97) + posicion);
  return String(posicion + 1);
}

/** "Rellenar": completa los nodos de forma consecutiva a partir del valor del nodo 1. */
function calcularRelleno(estilo, mayusculas, primero, cantidad) {
  const texto = primero.trim();
  if (!texto) return { error: "Escribe primero el valor del nodo 1." };

  if (estilo === "letras") {
    if (!/^[A-Za-z]$/.test(texto)) return { error: "El nodo 1 debe ser una letra." };
    const inicio = (mayusculas ? texto.toUpperCase() : texto.toLowerCase()).charCodeAt(0);
    const ultima = (mayusculas ? "Z" : "z").charCodeAt(0);
    if (inicio + cantidad - 1 > ultima) {
      return {
        error: `Desde la letra ${String.fromCharCode(ultima - cantidad + 2)} no alcanza para ${cantidad} nodos. ` +
          `La última letra desde la que se puede empezar es ${String.fromCharCode(ultima - cantidad + 1)}.`,
      };
    }
    return { valores: Array.from({ length: cantidad }, (_, i) => String.fromCharCode(inicio + i)) };
  }

  const inicio = parseInt(texto, 10);
  const maximo = estilo === "numeros" ? 999 : 99;
  if (inicio + cantidad - 1 > maximo) {
    return {
      error: `Desde el número ${maximo - cantidad + 2} no alcanza para ${cantidad} nodos. ` +
        `El último número desde el que se puede empezar es ${maximo - cantidad + 1}.`,
    };
  }
  return { valores: Array.from({ length: cantidad }, (_, i) => String(inicio + i)) };
}

/** "Aceptar": valida los campos y devuelve { nombres } o { error }. Rechaza nombres repetidos. */
function construirNombres(estilo, mayusculas, prefijo, valores) {
  if (estilo === "prefijo" && !prefijo) return { error: "Escribe la letra del prefijo." };

  const limpios = valores.map((v) => v.trim());
  const vacio = limpios.findIndex((v) => v === "");
  if (vacio >= 0) return { error: `El nodo ${vacio + 1} no tiene valor.` };

  let nombres;
  if (estilo === "letras") {
    nombres = limpios.map((v) => (mayusculas ? v.toUpperCase() : v.toLowerCase()));
  } else if (estilo === "numeros") {
    nombres = limpios.map((v) => String(parseInt(v, 10)));
  } else {
    const numeros = limpios.map((v) => parseInt(v, 10));
    const digitos = Math.max(...numeros) >= 10 ? 2 : 1;      // si alguno es 10 o más, todos con 2 dígitos (Q01…Q12)
    nombres = numeros.map((x) => prefijo + String(x).padStart(digitos, "0"));
  }

  const vistos = new Map();
  for (let i = 0; i < nombres.length; i++) {
    if (vistos.has(nombres[i])) {
      return { error: `El nombre «${nombres[i]}» está repetido en los nodos ${vistos.get(nombres[i]) + 1} y ${i + 1}.` };
    }
    vistos.set(nombres[i], i);
  }
  return { nombres };
}

/** Detecta el estilo de los nombres actuales para abrir el modal con ese estilo. null = estilo mixto. */
function detectarEstiloNombres(actuales) {
  if (actuales.every((x) => /^[A-Z]$/.test(x))) return { estilo: "letras", caso: "mayusculas" };
  if (actuales.every((x) => /^[a-z]$/.test(x))) return { estilo: "letras", caso: "minusculas" };
  if (actuales.every((x) => /^\d+$/.test(x) && +x >= 1 && +x <= 999)) return { estilo: "numeros" };

  const prefijos = actuales.map((x) => (/^[A-Za-z]\d+$/.test(x) && +x.slice(1) >= 1 && +x.slice(1) <= 99 ? x[0] : null));
  if (prefijos.every((p) => p !== null) && new Set(prefijos).size === 1) return { estilo: "prefijo", prefijo: prefijos[0] };
  return null;
}
/* ============ NOMBRES_LOGICA_FIN ============ */

/* ============ INTERFAZ DEL MODAL ============ */
const AYUDA_NOMBRES = {
  numeros: "Escribe un número del 1 al 999 en cada nodo.",
  letras: "Escribe una letra en cada nodo (se ajusta sola a mayúscula o minúscula).",
  prefijo: "Escribe la letra del prefijo y un número del 1 al 99 en cada nodo. " +
    "Si algún número es 10 o más, todos quedan con 2 dígitos (Q01, Q02… Q12).",
};

const estiloNombres = () => $("select-estilo-nombres").value;
const mayusculasNombres = () => $("select-caso-nombres").value === "mayusculas";
const camposNombres = () => [...$("grilla-nombres").querySelectorAll("input")];

function mostrarErrorNombres(mensaje) {
  const caja = $("error-nombres");
  caja.textContent = mensaje || "";
  caja.classList.toggle("oculto", !mensaje);
}

/** Un <input> por cada nodo actual (n). */
function construirGrillaNombres() {
  $("grilla-nombres").replaceChildren(...Array.from({ length: n }, (_, i) => crearElemento("label", { className: "campo-nodo" },
    crearElemento("span", { className: "campo-nodo__nombre", texto: `Nodo ${i + 1}` }),
    crearElemento("span", { className: "campo-nodo__prefijo", "aria-hidden": "true" }),
    crearElemento("input", {
      type: "text", className: "campo-nodo__input", autocomplete: "off", spellcheck: "false", "aria-label": `Nombre del nodo ${i + 1}`,
    }))));
}

/** Muestra u oculta las opciones según el estilo: "Letras en" solo con Letras, prefijo solo con Prefijo + número. */
function actualizarOpcionesNombres() {
  const estilo = estiloNombres();
  $("campo-caso-nombres").classList.toggle("oculto", estilo !== "letras");
  $("campo-prefijo-nombres").classList.toggle("oculto", estilo !== "prefijo");
  $("ayuda-nombres").textContent = `${AYUDA_NOMBRES[estilo]} Con «Rellenar» se completan los demás nodos a partir del primero.`;

  const prefijo = estilo === "prefijo" ? $("input-prefijo-nombres").value : "";
  $("grilla-nombres").querySelectorAll(".campo-nodo__prefijo").forEach((s) => { s.textContent = prefijo; });
  camposNombres().forEach((campo) => campo.setAttribute("inputmode", estilo === "letras" ? "text" : "numeric"));
}

/** "Por defecto": nombres consecutivos del estilo elegido (A, B, C… o 1, 2, 3…). */
function aplicarPorDefectoNombres() {
  const estilo = estiloNombres();
  if (estilo === "prefijo" && !$("input-prefijo-nombres").value) $("input-prefijo-nombres").value = "Q";
  camposNombres().forEach((campo, i) => { campo.value = valorPorDefectoNodo(i, estilo, mayusculasNombres()); });
  actualizarOpcionesNombres();
  mostrarErrorNombres("");
}

function rellenarNombres() {
  const campos = camposNombres();
  const resultado = calcularRelleno(estiloNombres(), mayusculasNombres(), campos[0].value, n);
  if (resultado.error) return mostrarErrorNombres(resultado.error);
  campos.forEach((campo, i) => { campo.value = resultado.valores[i]; });
  mostrarErrorNombres("");
}

function aceptarNombres() {
  const resultado = construirNombres(estiloNombres(), mayusculasNombres(), $("input-prefijo-nombres").value, camposNombres().map((c) => c.value));
  if (resultado.error) return mostrarErrorNombres(resultado.error);

  etiquetas = resultado.nombres;
  cerrarModal("modal-nombres");
  renderizarMatriz();
  dibujarGrafo();
  mostrarToast("Nombres de los nodos actualizados");
}

function abrirModalNombres() {
  construirGrillaNombres();
  const detectado = detectarEstiloNombres(etiquetas);

  $("select-estilo-nombres").value = detectado ? detectado.estilo : "numeros";
  $("select-caso-nombres").value = detectado && detectado.caso ? detectado.caso : "mayusculas";
  $("input-prefijo-nombres").value = detectado && detectado.prefijo ? detectado.prefijo : "Q";

  if (detectado) {                     // se conservan los nombres actuales
    camposNombres().forEach((campo, i) => {
      campo.value = detectado.estilo === "prefijo" ? etiquetas[i].slice(1) : etiquetas[i];
    });
    actualizarOpcionesNombres();
    mostrarErrorNombres("");
  } else {                             // nombres mezclados: se parte de los valores por defecto
    aplicarPorDefectoNombres();
  }
  abrirModal("modal-nombres");
  $("select-estilo-nombres").focus();
}

function inicializarNombres() {
  $("btn-nombrar").addEventListener("click", abrirModalNombres);

  // Al cambiar el estilo se reinician los nombres; al cambiar mayúsculas/minúsculas se convierten
  $("select-estilo-nombres").addEventListener("change", aplicarPorDefectoNombres);
  $("select-caso-nombres").addEventListener("change", () => {
    camposNombres().forEach((campo) => { campo.value = filtrarValorNodo(campo.value, "letras", mayusculasNombres()); });
  });

  // El prefijo es una sola letra (se respeta q o Q)
  $("input-prefijo-nombres").addEventListener("input", (e) => {
    e.target.value = ultimaLetra(e.target.value);
    actualizarOpcionesNombres();
  });

  // Filtro en cada campo de nodo (delegación de eventos); Enter acepta
  $("grilla-nombres").addEventListener("input", (e) => {
    e.target.value = filtrarValorNodo(e.target.value, estiloNombres(), mayusculasNombres());
    mostrarErrorNombres("");
  });
  $("grilla-nombres").addEventListener("keydown", (e) => { if (e.key === "Enter") aceptarNombres(); });

  $("btn-nombres-defecto").addEventListener("click", aplicarPorDefectoNombres);
  $("btn-nombres-rellenar").addEventListener("click", rellenarNombres);
  $("btn-nombres-aceptar").addEventListener("click", aceptarNombres);
  $("btn-nombres-cancelar").addEventListener("click", () => cerrarModal("modal-nombres"));
  $("modal-nombres").addEventListener("click", (e) => { if (e.target === $("modal-nombres")) cerrarModal("modal-nombres"); });
}

inicializarNombres();


/* ==========================================================================
   EDITAR ARISTA (MANUAL) · modal con Origen, Destino, Agregar, Quitar y Cerrar
   ========================================================================== */

IDS_MODALES.push("modal-arista");     // para que Escape también cierre este modal

/** Llena un <select> con las etiquetas actuales (valor = índice del nodo). */
function llenarSelectNodos(select, indiceInicial) {
  select.replaceChildren(...etiquetas.map((nombre, i) => crearElemento("option", { value: String(i), texto: nombre })));
  select.value = String(indiceInicial);
}

function mostrarMensajeArista(texto) {
  $("mensaje-arista").textContent = texto;
}

function abrirModalArista() {
  llenarSelectNodos($("select-origen"), 0);
  llenarSelectNodos($("select-destino"), Math.min(1, n - 1));
  mostrarMensajeArista("");
  abrirModal("modal-arista");
  $("select-origen").focus();
}

/** Origen y destino elegidos. Pueden ser el mismo nodo: esa arista es un bucle (diagonal de la matriz). */
function leerParDeArista() {
  const origen = Number($("select-origen").value);
  const destino = Number($("select-destino").value);
  return [origen, destino];
}

function agregarAristaManual() {
  const par = leerParDeArista();
  if (!par) return;
  const [o, d] = par;
  if (matriz[o][d] === 1) {
    mostrarMensajeArista(`La conexión ${etiquetas[o]} → ${etiquetas[d]} ya existe.`);
    return;
  }
  matriz[o][d] = 1;
  renderizarMatriz();
  dibujarGrafo();
  mostrarMensajeArista("");
  mostrarToast(`Arista ${etiquetas[o]} → ${etiquetas[d]} agregada`);
}

function quitarAristaManual() {
  const par = leerParDeArista();
  if (!par) return;
  const [o, d] = par;
  if (matriz[o][d] === 0) {
    mostrarMensajeArista(`La conexión ${etiquetas[o]} → ${etiquetas[d]} no existe.`);
    return;
  }
  matriz[o][d] = 0;
  renderizarMatriz();
  dibujarGrafo();
  mostrarMensajeArista("");
  mostrarToast(`Arista ${etiquetas[o]} → ${etiquetas[d]} quitada`);
}

function inicializarEditarArista() {
  $("btn-editar-arista-manual").addEventListener("click", abrirModalArista);
  $("btn-arista-agregar").addEventListener("click", agregarAristaManual);     // no cierran el modal
  $("btn-arista-quitar").addEventListener("click", quitarAristaManual);
  $("btn-arista-cerrar").addEventListener("click", () => cerrarModal("modal-arista"));
  ["select-origen", "select-destino"].forEach((id) => $(id).addEventListener("change", () => mostrarMensajeArista("")));
  $("modal-arista").addEventListener("click", (e) => { if (e.target === $("modal-arista")) cerrarModal("modal-arista"); });
}

inicializarEditarArista();


/* ==========================================================================
   ANÁLISIS DE NODO · a qué nodos llega directamente el nodo elegido
   ========================================================================== */

/** Llena #select-analisis con las etiquetas actuales y conserva el nodo elegido (si sigue existiendo). */
function actualizarSelectAnalisis() {
  const select = $("select-analisis");
  const previo = Number(select.value);
  const indice = Number.isInteger(previo) && previo >= 0 && previo < etiquetas.length ? previo : 0;
  llenarSelectNodos(select, indice);
  $("texto-analisis").textContent = "";      // el resultado anterior pudo quedar desactualizado
}

function analizarNodo() {
  const salida = $("texto-analisis");
  const idx = Number($("select-analisis").value);
  if (!Number.isInteger(idx) || idx < 0 || idx >= n) {
    salida.textContent = "Elige un nodo de la lista.";
    return;
  }

  const destinos = [];
  matriz[idx].forEach((valor, j) => { if (valor === 1) destinos.push(`${etiquetas[idx]}->${etiquetas[j]}`); });

  salida.textContent = `Nodo actual: ${etiquetas[idx]}\nConexiones: ${destinos.length ? destinos.join(", ") : "Ninguna"}`;
}

function inicializarAnalisis() {
  $("btn-analizar").addEventListener("click", analizarNodo);
}

inicializarAnalisis();


/* ==========================================================================
   MODO EDICIÓN IN-PLACE · grafo bloqueado → Editar → Aceptar / Cancelar
   (las variables matriz_backup, etiquetas_backup, posiciones_backup y
   modoEdicionActivo están declaradas arriba, en el estado global)
   ========================================================================== */

// Mientras se edita, estos botones se deshabilitan: usan o abandonan el grafo y dejarían el modo edición a medias
const IDS_BLOQUEADOS_EN_EDICION = ["btn-guardar", "btn-volver-inicio", "btn-ejecutar"];

/** Refleja `modoEdicionActivo` en la interfaz: botones, panel, bloqueo del lienzo, texto, matriz y grafo. */
function aplicarEstadoEdicion() {
  $("btn-abrir-edicion").classList.toggle("oculto", modoEdicionActivo);
  $("panel-edicion").classList.toggle("oculto", !modoEdicionActivo);
  lienzo.dataset.bloqueado = String(!modoEdicionActivo);
  IDS_BLOQUEADOS_EN_EDICION.forEach((id) => {
    $(id).disabled = modoEdicionActivo;
  });

  // Se descarta cualquier arrastre o resaltado pendiente del lienzo
  nodoArrastrado = null;
  nodoOrigen = null;
  puntoActual = null;
  nodoHover = null;
  lienzo.style.cursor = "";

  actualizarTextoModo();
  renderizarMatriz();      // las celdas solo son editables en modo edición
  dibujarGrafo();
}

/** Guarda una copia (de valores, no de referencias) del grafo y abre las herramientas. */
function abrirEdicion() {
  matriz_backup = matriz.map((fila) => fila.slice());
  etiquetas_backup = etiquetas.slice();
  posiciones_backup = posiciones ? posiciones.map((p) => p.slice()) : null;
  modoEdicionActivo = true;
  aplicarModoHerramienta("aristas");
  aplicarEstadoEdicion();
}

/** Conserva los cambios (ya están en matriz, etiquetas y posiciones) y vuelve a bloquear. */
function aceptarEdicion() {
  modoEdicionActivo = false;
  matriz_backup = etiquetas_backup = posiciones_backup = null;
  aplicarEstadoEdicion();
}

/** Descarta los cambios: restaura el grafo desde los respaldos y vuelve a bloquear. */
function cancelarEdicion() {
  if (matriz_backup) {
    matriz = matriz_backup.map((fila) => fila.slice());
    etiquetas = etiquetas_backup.slice();
    posiciones = posiciones_backup ? posiciones_backup.map((p) => p.slice()) : null;
  }
  modoEdicionActivo = false;
  matriz_backup = etiquetas_backup = posiciones_backup = null;
  aplicarEstadoEdicion();  // incluye renderizarMatriz() y dibujarGrafo()
}

function inicializarEdicion() {
  $("btn-abrir-edicion").addEventListener("click", abrirEdicion);
  $("btn-aceptar-edicion").addEventListener("click", aceptarEdicion);
  $("btn-cancelar-edicion").addEventListener("click", cancelarEdicion);
}

inicializarEdicion();


/* ==========================================================================
   FONDO ANIMADO · red de nodos ("constelación") en un canvas nativo
   ========================================================================== */
function iniciarFondoNodos() {
  const canvas = $("canvas-fondo");
  if (!canvas) return;
  const c = canvas.getContext("2d");

  const DISTANCIA_MAX = 150;      // px: por debajo de esta distancia se unen dos nodos con una línea
  const RADIO = 1.5;              // px
  const VELOCIDAD_MAX = 0.6;      // px por cuadro (a 60 fps), en cada eje: entre -0.5 y 0.5
  const ALFA_NODO = 0.35;
  const ALFA_LINEA_MAX = 0.35;    
  const color = (alfa) => `rgba(37, 19, 62, ${alfa})`;
  const movimientoReducido = window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches;

  let ancho = window.innerWidth;
  let alto = window.innerHeight;
  const cantidad = Math.min(70, Math.max(50, Math.round((ancho * alto) / 25000)));   // entre 50 y 70 según el tamaño de la ventana
  const particulas = Array.from({ length: cantidad }, () => ({
    x: Math.random() * ancho,
    y: Math.random() * alto,
    vx: (Math.random() - 0.5) * 2 * VELOCIDAD_MAX,
    vy: (Math.random() - 0.5) * 2 * VELOCIDAD_MAX,
  }));

  function ajustarTamano() {
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    ancho = window.innerWidth;
    alto = window.innerHeight;
    canvas.width = ancho * dpr;
    canvas.height = alto * dpr;
    c.setTransform(dpr, 0, 0, dpr, 0, 0);
    particulas.forEach((p) => {                 // si la ventana se encoge, nadie queda fuera
      p.x = Math.min(p.x, ancho);
      p.y = Math.min(p.y, alto);
    });
    if (movimientoReducido) dibujar();          // sin animación, se redibuja el cuadro fijo
  }

  function dibujar() {
    c.clearRect(0, 0, ancho, alto);

    c.lineWidth = 1;
    for (let i = 0; i < particulas.length; i++) {
      for (let j = i + 1; j < particulas.length; j++) {
        const distancia = Math.hypot(particulas[i].x - particulas[j].x, particulas[i].y - particulas[j].y);
        if (distancia >= DISTANCIA_MAX) continue;
        c.strokeStyle = color(ALFA_LINEA_MAX * (1 - distancia / DISTANCIA_MAX));
        c.beginPath();
        c.moveTo(particulas[i].x, particulas[i].y);
        c.lineTo(particulas[j].x, particulas[j].y);
        c.stroke();
      }
    }

    c.fillStyle = color(ALFA_NODO);
    particulas.forEach((p) => {
      c.beginPath();
      c.arc(p.x, p.y, RADIO, 0, 2 * Math.PI);
      c.fill();
    });
  }

  let ultimoCuadro = performance.now();
  function cuadro(ahora) {
    const dt = Math.min((ahora - ultimoCuadro) / 16.667, 3);    // mismo ritmo en pantallas de 60, 120 o 144 Hz
    ultimoCuadro = ahora;

    particulas.forEach((p) => {
      p.x += p.vx * dt;
      p.y += p.vy * dt;
      if (p.x < 0 || p.x > ancho) { p.vx *= -1; p.x = Math.min(Math.max(p.x, 0), ancho); }     // rebote en los bordes
      if (p.y < 0 || p.y > alto) { p.vy *= -1; p.y = Math.min(Math.max(p.y, 0), alto); }
    });
    dibujar();
    requestAnimationFrame(cuadro);
  }

  window.addEventListener("resize", ajustarTamano);
  ajustarTamano();
  if (!movimientoReducido) requestAnimationFrame(cuadro);
}

iniciarFondoNodos();
