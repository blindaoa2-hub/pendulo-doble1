"use strict";
/* ============================================================
   SIMULADOR: PÉNDULO DOBLE Y MOVIMIENTO CAÓTICO
   Modelo: Lagrangiano L = T - V, integrado con Runge-Kutta 4.
   Ángulos medidos desde la vertical hacia abajo (radianes).
   ============================================================ */
const $ = id => document.getElementById(id);
const DT = 0.001;          // paso de integración (s)
const UMBRAL = 0.5;        // separación (m) a partir de la cual se declara divergencia
const VENTANA = 20;        // segundos visibles en las gráficas
const RANGOS = { m1:[0.1,5], m2:[0.1,5], L1:[0.5,3], L2:[0.5,3], th1:[-180,180], th2:[-180,180],
                 w1:[-10,10], w2:[-10,10], g:[1,25], b:[0,1] };
const INICIALES = ["th1","th2","w1","w2"];   // al cambiarlas se reinicia la simulación
const PRESETS = {
  pequenas:  { m1:1, m2:1, L1:1, L2:1, th1:5,   th2:5,   w1:0, w2:0, g:9.81 },
  caotico:   { m1:1, m2:1, L1:1, L2:1, th1:120, th2:-10, w1:0, w2:0, g:9.81 },
  invertido: { m1:1, m2:1, L1:1, L2:1, th1:178, th2:178, w1:0, w2:0, g:9.81 }
};

/* ---------- Estado ---------- */
let P, A, B, t = 0, corriendo = false, E0 = 0, Emin = 0, tDiv = null, ensayos = 0, fallo = false;
let hist = [], estelaA = [], estelaB = [];

/* ---------- 1. Lectura de datos del usuario ---------- */
const val = id => parseFloat($("n-" + id).value);
const comparando = () => $("chk-comparar").checked;
function leerParametros() {
  return { m1: val("m1"), m2: val("m2"), L1: val("L1"), L2: val("L2"), g: val("g"),
           b: $("chk-amort").checked ? val("b") : 0 };
}
function leerInicial() {
  const r = Math.PI / 180;
  return { th1: val("th1") * r, th2: val("th2") * r, w1: val("w1"), w2: val("w2") };
}
function leerDelta() {
  const d = parseFloat($("n-dth").value);
  return Number.isFinite(d) ? Math.min(0.1, Math.max(0.0001, d)) : 0.001;
}

/* ---------- 2. Física: ecuaciones de movimiento ---------- */
// Aceleraciones angulares (α1, α2) obtenidas de Euler-Lagrange. Se añade -b·ω si hay amortiguamiento.
function aceleraciones(s, p) {
  const d = s.th1 - s.th2, den = 2*p.m1 + p.m2 - p.m2*Math.cos(2*d);
  const a1 = (-p.g*(2*p.m1 + p.m2)*Math.sin(s.th1) - p.m2*p.g*Math.sin(s.th1 - 2*s.th2)
            - 2*Math.sin(d)*p.m2*(s.w2*s.w2*p.L2 + s.w1*s.w1*p.L1*Math.cos(d))) / (p.L1*den);
  const a2 = (2*Math.sin(d)*(s.w1*s.w1*p.L1*(p.m1 + p.m2) + p.g*(p.m1 + p.m2)*Math.cos(s.th1)
            + s.w2*s.w2*p.L2*p.m2*Math.cos(d))) / (p.L2*den);
  return [a1 - p.b*s.w1, a2 - p.b*s.w2];
}
const derivada = (y, p) => {
  const [a1, a2] = aceleraciones({ th1:y[0], th2:y[1], w1:y[2], w2:y[3] }, p);
  return [y[2], y[3], a1, a2];
};
// Un paso de Runge-Kutta de 4.º orden (modifica el estado s)
function rk4(s, p, h) {
  const y = [s.th1, s.th2, s.w1, s.w2];
  const mas = (y, k, c) => y.map((v, i) => v + c*k[i]);
  const k1 = derivada(y, p), k2 = derivada(mas(y, k1, h/2), p);
  const k3 = derivada(mas(y, k2, h/2), p), k4 = derivada(mas(y, k3, h), p);
  const n = y.map((v, i) => v + h/6*(k1[i] + 2*k2[i] + 2*k3[i] + k4[i]));
  s.th1 = n[0]; s.th2 = n[1]; s.w1 = n[2]; s.w2 = n[3];
}
// Energías: T cinética, V potencial (cero en el pivote), E = T + V
function energias(s, p) {
  const T = 0.5*p.m1*p.L1**2*s.w1**2 +
            0.5*p.m2*(p.L1**2*s.w1**2 + p.L2**2*s.w2**2 + 2*p.L1*p.L2*s.w1*s.w2*Math.cos(s.th1 - s.th2));
  const V = -(p.m1 + p.m2)*p.g*p.L1*Math.cos(s.th1) - p.m2*p.g*p.L2*Math.cos(s.th2);
  return { T, V, E: T + V };
}
// Posición, velocidad y aceleración lineal de las dos masas (eje y hacia arriba)
function cinematica(s, p) {
  const [al1, al2] = aceleraciones(s, p);
  const x1 = p.L1*Math.sin(s.th1), y1 = -p.L1*Math.cos(s.th1);
  const x2 = x1 + p.L2*Math.sin(s.th2), y2 = y1 - p.L2*Math.cos(s.th2);
  const vx1 = p.L1*s.w1*Math.cos(s.th1), vy1 = p.L1*s.w1*Math.sin(s.th1);
  const vx2 = vx1 + p.L2*s.w2*Math.cos(s.th2), vy2 = vy1 + p.L2*s.w2*Math.sin(s.th2);
  const ax1 = p.L1*(al1*Math.cos(s.th1) - s.w1**2*Math.sin(s.th1));
  const ay1 = p.L1*(al1*Math.sin(s.th1) + s.w1**2*Math.cos(s.th1));
  const ax2 = ax1 + p.L2*(al2*Math.cos(s.th2) - s.w2**2*Math.sin(s.th2));
  const ay2 = ay1 + p.L2*(al2*Math.sin(s.th2) + s.w2**2*Math.cos(s.th2));
  return { x1, y1, x2, y2, v1: Math.hypot(vx1, vy1), v2: Math.hypot(vx2, vy2),
           a1: Math.hypot(ax1, ay1), a2: Math.hypot(ax2, ay2) };
}
const separacion = () => {
  const a = cinematica(A, P), b = cinematica(B, P);
  return Math.hypot(a.x2 - b.x2, a.y2 - b.y2);
};
// Referencia de energía: deriva (%) = (E - E0) / (E0 - Emin) · 100, con Emin = energía en reposo abajo
function fijarReferencia() {
  E0 = energias(A, P).E;
  Emin = -(P.m1 + P.m2)*P.g*P.L1 - P.m2*P.g*P.L2;
}
const deriva = () => (energias(A, P).E - E0) / (E0 - Emin) * 100;

/* ---------- 3. Control de la simulación ---------- */
function reiniciar() {
  corriendo = false; fallo = false; t = 0; tDiv = null;
  P = leerParametros();
  const i = leerInicial();
  A = { ...i }; B = { ...i, th1: i.th1 + leerDelta() };
  fijarReferencia();
  hist = []; estelaA = []; estelaB = [];
  guardarPunto(); actualizar();
}
function avanzar(dtReal) {
  const n = Math.max(1, Math.round(Math.min(dtReal, 0.05) / DT));
  for (let i = 0; i < n; i++) {
    rk4(A, P, DT);
    if (comparando()) rk4(B, P, DT);
    t += DT;
    if (tDiv === null && comparando() && separacion() > UMBRAL) tDiv = t;
  }
  if (![A.th1, A.th2, A.w1, A.w2].every(Number.isFinite)) { corriendo = false; fallo = true; }
}
function guardarPunto() {
  const e = energias(A, P), c = cinematica(A, P);
  hist.push({ t, th1: A.th1, th2: A.th2, w1: A.w1, w2: A.w2, T: e.T, V: e.V, E: e.E,
              thB: B.th1, wB: B.w1 });
  estelaA.push([c.x2, c.y2]);
  if (comparando()) { const d = cinematica(B, P); estelaB.push([d.x2, d.y2]); }
  if (hist.length > 2500) hist.splice(0, 500);
  if (estelaA.length > 1500) estelaA.splice(0, 300);
  if (estelaB.length > 1500) estelaB.splice(0, 300);
}
let ultimo = null;
function bucle(ts) {
  if (corriendo) {
    avanzar(ultimo === null ? 0.016 : (ts - ultimo) / 1000);
    guardarPunto(); actualizar();
  }
  ultimo = ts; requestAnimationFrame(bucle);
}

/* ---------- 4. Representación: animación ---------- */
function dibujarAnimacion() {
  const c = $("cv-anim"), g = c.getContext("2d"), W = c.width, H = c.height;
  const cx = W/2, cy = H/2, esc = 0.46*W/(P.L1 + P.L2);
  const X = x => cx + x*esc, Y = y => cy - y*esc;
  g.clearRect(0, 0, W, H);
  g.strokeStyle = "#2a3a47"; g.beginPath(); g.arc(cx, cy, (P.L1 + P.L2)*esc, 0, 7); g.stroke();
  const estela = (pts, rgb) => {
    if (!$("chk-rastro").checked) return;
    for (let i = 1; i < pts.length; i++) {
      g.strokeStyle = `rgba(${rgb},${(i/pts.length).toFixed(2)})`; g.lineWidth = 1.5;
      g.beginPath(); g.moveTo(X(pts[i-1][0]), Y(pts[i-1][1])); g.lineTo(X(pts[i][0]), Y(pts[i][1])); g.stroke();
    }
  };
  const pendulo = (s, color) => {
    const k = cinematica(s, P);
    g.strokeStyle = color; g.lineWidth = 3; g.beginPath();
    g.moveTo(cx, cy); g.lineTo(X(k.x1), Y(k.y1)); g.lineTo(X(k.x2), Y(k.y2)); g.stroke();
    g.fillStyle = color;
    [[k.x1, k.y1, P.m1], [k.x2, k.y2, P.m2]].forEach(([x, y, m]) => {
      g.beginPath(); g.arc(X(x), Y(y), 6 + 4*Math.sqrt(m), 0, 7); g.fill();
    });
  };
  estela(estelaA, "242,163,58");
  if (comparando()) estela(estelaB, "224,82,127");
  if (comparando()) pendulo(B, "#e0527f");
  pendulo(A, "#f2a33a");
  g.fillStyle = "#fff"; g.beginPath(); g.arc(cx, cy, 4, 0, 7); g.fill();
}

/* ---------- 5. Representación: gráficas ---------- */
// Dibuja series {xs, ys, color} con ejes autoajustables; rompe la línea si hay saltos grandes en x (fase)
function trazar(id, series, xr, xl, yl, salto) {
  const c = $(id), g = c.getContext("2d"), W = c.width, H = c.height;
  const m = { l: 40, r: 8, t: 8, b: 20 };
  g.clearRect(0, 0, W, H);
  let y0 = Infinity, y1 = -Infinity;
  series.forEach(s => s.ys.forEach(v => { if (v < y0) y0 = v; if (v > y1) y1 = v; }));
  if (!Number.isFinite(y0) || y0 === y1) { y0 = (y0 || 0) - 1; y1 = (y1 || 0) + 1; }
  const pad = (y1 - y0)*0.08; y0 -= pad; y1 += pad;
  const X = x => m.l + (x - xr[0])/(xr[1] - xr[0])*(W - m.l - m.r);
  const Y = y => H - m.b - (y - y0)/(y1 - y0)*(H - m.t - m.b);
  g.strokeStyle = "#3b4d5b"; g.lineWidth = 1;
  g.strokeRect(m.l, m.t, W - m.l - m.r, H - m.t - m.b);
  if (y0 < 0 && y1 > 0) { g.beginPath(); g.moveTo(m.l, Y(0)); g.lineTo(W - m.r, Y(0)); g.stroke(); }
  g.fillStyle = "#9fb3c0"; g.font = "10px sans-serif"; g.textAlign = "right";
  g.fillText(y1.toFixed(1), m.l - 3, m.t + 8); g.fillText(y0.toFixed(1), m.l - 3, H - m.b);
  g.textAlign = "center";
  g.fillText(xr[0].toFixed(0), m.l, H - 8); g.fillText(xr[1].toFixed(0), W - m.r, H - 8);
  g.fillText(xl, W/2, H - 2); g.textAlign = "left"; g.fillText(yl, 2, 10);
  series.forEach(s => {
    g.strokeStyle = s.color; g.lineWidth = 1.4; g.beginPath();
    s.xs.forEach((x, i) => {
      if (x < xr[0] || x > xr[1]) return;
      const nuevo = i === 0 || (salto && Math.abs(x - s.xs[i-1]) > salto) || s.xs[i-1] < xr[0];
      nuevo ? g.moveTo(X(x), Y(s.ys[i])) : g.lineTo(X(x), Y(s.ys[i]));
    });
    g.stroke();
  });
}
function dibujarGraficas() {
  const x0 = Math.max(0, t - VENTANA), xr = [x0, x0 + VENTANA];
  const ts = hist.map(h => h.t), col = k => hist.map(h => h[k]);
  const ang = v => v.map(a => Math.atan2(Math.sin(a), Math.cos(a)));
  trazar("cv-theta", [{ xs: ts, ys: col("th1"), color: "#f2a33a" }, { xs: ts, ys: col("th2"), color: "#5ec8d8" }], xr, "t (s)", "θ (rad)");
  trazar("cv-omega", [{ xs: ts, ys: col("w1"), color: "#f2a33a" }, { xs: ts, ys: col("w2"), color: "#5ec8d8" }], xr, "t (s)", "ω (rad/s)");
  trazar("cv-energia", [{ xs: ts, ys: col("T"), color: "#5ec8d8" }, { xs: ts, ys: col("V"), color: "#7bd88f" },
                         { xs: ts, ys: col("E"), color: "#ffffff" }], xr, "t (s) · T azul, V verde, E blanco", "E (J)");
  const fases = [{ xs: ang(col("th1")), ys: col("w1"), color: "#f2a33a" }];
  if (comparando()) fases.push({ xs: ang(col("thB")), ys: col("wB"), color: "#e0527f" });
  trazar("cv-fases", fases, [-Math.PI, Math.PI], "θ₁ (rad)", "ω₁ (rad/s)", Math.PI);
}

/* ---------- 6. Resultados y mensajes ---------- */
const f = (n, d = 2) => { if (!Number.isFinite(n)) return "—"; const r = n.toFixed(d); return Number(r) === 0 ? (0).toFixed(d) : r; };   // evita «-0.0000»
function mostrarResultados() {
  const k = cinematica(A, P), e = energias(A, P);
  const set = (id, v, d) => { $("out-" + id).textContent = f(v, d); };
  set("t", t); set("x1", k.x1); set("y1", k.y1); set("x2", k.x2); set("y2", k.y2);
  set("v1", k.v1); set("v2", k.v2); set("a1", k.a1); set("a2", k.a2);
  set("w1", A.w1); set("w2", A.w2); set("T", e.T); set("V", e.V); set("E", e.E);
  set("deriva", deriva(), 4); set("sep", comparando() ? separacion() : NaN, 3);
  // Evaluación en vivo de las ecuaciones de movimiento (sección «Fórmulas»)
  const [al1, al2] = aceleraciones(A, P), dl = A.th1 - A.th2;
  set("delta", dl); set("D", 2*P.m1 + P.m2 - P.m2*Math.cos(2*dl), 3); set("al1", al1); set("al2", al2);
}
function mostrarMensaje() {
  const m = $("mensaje"); m.className = "mensaje";
  if (fallo) { m.textContent = "Se produjo un valor no válido. Pulsa Reiniciar y revisa los parámetros."; m.classList.add("caos"); }
  else if (!comparando()) m.textContent = "Comparación desactivada: activa el segundo péndulo para estudiar la sensibilidad.";
  else if (tDiv !== null) {
    m.textContent = `Movimiento caótico: A y B partieron con una diferencia de ${leerDelta()} rad en θ₁ y divergieron en t = ${tDiv.toFixed(2)} s.`;
    m.classList.add("caos");
  } else if (t === 0) m.textContent = "Listo. Pulsa Iniciar para comenzar la simulación.";
  else { m.textContent = `Los péndulos aún se mueven casi igual (separación ${f(separacion(), 3)} m).`; m.classList.add("regular"); }
}
function actualizar() { dibujarAnimacion(); dibujarGraficas(); mostrarResultados(); mostrarMensaje(); }

/* ---------- 7. Registro de ensayos ---------- */
function registrarEnsayo() {
  ensayos++;
  const i = leerInicial(), r = 180/Math.PI;
  const res = !comparando() ? "Comparación desactivada" : tDiv !== null ? tDiv.toFixed(2) : `No divergió (t = ${t.toFixed(1)})`;
  const fila = $("tbody-ensayos").insertRow();
  [ensayos, `${P.m1}, ${P.m2}`, `${P.L1}, ${P.L2}`, `${f(i.th1*r, 0)}, ${f(i.th2*r, 0)}`, P.g, res]
    .forEach(v => { fila.insertCell().textContent = v; });
}

/* ---------- 8. Validación científica ---------- */
function pruebaEnergia() {            // conservación de E durante 10 s (sin amortiguamiento)
  const p = { m1:1, m2:1, L1:1, L2:1, g:9.81, b:0 };
  const s = { th1: 2*Math.PI/3, th2: -10*Math.PI/180, w1: 0, w2: 0 };
  const e0 = energias(s, p).E, emin = -(p.m1 + p.m2)*p.g*p.L1 - p.m2*p.g*p.L2;
  let max = 0;
  for (let i = 0; i < 10000; i++) {
    rk4(s, p, DT);
    if (i % 10 === 0) max = Math.max(max, Math.abs(energias(s, p).E - e0)/(e0 - emin)*100);
  }
  return max;
}
function pruebaModo(signo) {          // oscilaciones pequeñas: ω² = (g/L)(2 ± √2)
  const p = { m1:1, m2:1, L1:1, L2:1, g:9.81, b:0 };
  const lam = 2 + signo*Math.SQRT2, th = 0.01;
  const s = { th1: th, th2: th*2*(1 - lam)/lam, w1: 0, w2: 0 };
  const cruces = []; let prev = s.th1;
  for (let i = 1; i <= 20000; i++) {
    rk4(s, p, DT);
    if (prev*s.th1 < 0) cruces.push((i - 1 + prev/(prev - s.th1))*DT);
    prev = s.th1;
  }
  const n = cruces.length;
  const periodo = 2*(cruces[n-1] - cruces[0])/(n - 1);
  return { teorico: Math.sqrt(p.g/p.L1*lam), simulado: 2*Math.PI/periodo };
}
function pruebaDivergencia() {        // sensibilidad: Δθ₁ = 0,001 rad en el caso caótico
  const p = { m1:1, m2:1, L1:1, L2:1, g:9.81, b:0 };
  const a = { th1: 2*Math.PI/3, th2: -10*Math.PI/180, w1: 0, w2: 0 }, b = { ...a, th1: a.th1 + 0.001 };
  for (let i = 1; i <= 40000; i++) {
    rk4(a, p, DT); rk4(b, p, DT);
    const d = Math.hypot(p.L1*(Math.sin(a.th1) - Math.sin(b.th1)) + p.L2*(Math.sin(a.th2) - Math.sin(b.th2)),
                         p.L1*(Math.cos(a.th1) - Math.cos(b.th1)) + p.L2*(Math.cos(a.th2) - Math.cos(b.th2)));
    if (d > UMBRAL) return i*DT;
  }
  return null;
}
function validar() {
  const tb = $("tbody-validacion"); tb.innerHTML = "";
  const fila = v => { const r = tb.insertRow(); v.forEach(x => { r.insertCell().textContent = x; }); };
  const dE = pruebaEnergia();
  fila(["Conservación de E (10 s, máx. deriva)", "0 %", f(dE, 6) + " %", f(dE, 6)]);
  [["lento", -1], ["rápido", 1]].forEach(([n, sg]) => {
    const r = pruebaModo(sg);
    fila([`Modo normal ${n}: ω (rad/s)`, f(r.teorico, 4), f(r.simulado, 4), f(Math.abs(r.simulado - r.teorico)/r.teorico*100, 3)]);
  });
  const d = pruebaDivergencia();
  fila(["Sensibilidad: Δθ₁ = 0,001 rad (t de divergencia)", "Debe divergir (caos)", d ? `t = ${d.toFixed(2)} s` : "No divergió en 40 s", "—"]);
}

/* ---------- 9. Eventos: enlazar controles ---------- */
function sincronizarPlaneta() {
  const o = [...$("planeta").options].find(x => x.value !== "custom" && Math.abs(parseFloat(x.value) - val("g")) < 0.005);
  $("planeta").value = o ? o.value : "custom";
}
function cambio(id) {
  if (INICIALES.includes(id)) return reiniciar();
  P = leerParametros(); fijarReferencia();
  if (id === "g") sincronizarPlaneta();
  actualizar();
}
function fijar(id, v) {                 // asigna valor validado al deslizador y al campo numérico
  const [mn, mx] = RANGOS[id];
  let x = parseFloat(v); if (!Number.isFinite(x)) x = parseFloat($("r-" + id).value);
  x = Math.min(mx, Math.max(mn, x));
  $("r-" + id).value = x; $("n-" + id).value = x;
}
Object.keys(RANGOS).forEach(id => {
  $("r-" + id).addEventListener("input", e => { fijar(id, e.target.value); cambio(id); });
  $("n-" + id).addEventListener("change", e => { fijar(id, e.target.value); cambio(id); });
});
$("n-dth").addEventListener("change", reiniciar);
$("planeta").addEventListener("change", e => { if (e.target.value !== "custom") { fijar("g", e.target.value); cambio("g"); } });
$("chk-amort").addEventListener("change", () => cambio("b"));
$("chk-comparar").addEventListener("change", reiniciar);
$("chk-rastro").addEventListener("change", actualizar);
$("btn-iniciar").addEventListener("click", () => { if (!fallo) corriendo = true; });
$("btn-pausar").addEventListener("click", () => { corriendo = false; });
$("btn-reiniciar").addEventListener("click", reiniciar);
$("btn-borrar").addEventListener("click", () => { estelaA = []; estelaB = []; actualizar(); });
$("btn-registrar").addEventListener("click", registrarEnsayo);
$("btn-validar").addEventListener("click", validar);
document.querySelectorAll("[data-preset]").forEach(b => b.addEventListener("click", () => {
  Object.entries(PRESETS[b.dataset.preset]).forEach(([k, v]) => fijar(k, v));
  sincronizarPlaneta(); reiniciar();
}));

/* ---------- Inicio ---------- */
reiniciar();
requestAnimationFrame(bucle);
