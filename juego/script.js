"use strict";
/* ============================================================
   OBRA CAÓTICA: duelo de péndulos dobles (2 jugadores)
   Idea: arrastra y suelta el péndulo, empújalo y derriba bloques.
   Física: péndulo doble con Euler-Lagrange + Runge-Kutta 4.
   Los parámetros físicos son FIJOS (no se pueden cambiar).
   ============================================================ */
const $ = id => document.getElementById(id);
const cv = $("cv"), g = cv.getContext("2d"), W = cv.width, H = cv.height;

/* ---------- 1. Datos fijos ---------- */
const P = { m1: 1, m2: 1, L1: 1, L2: 1, g: 9.81 };      // kg, m, m/s²
const DT = 0.002;            // paso de integración (s)
const ESC = 190;             // píxeles por metro
const PX = W / 2, PY = 110;  // punto de suspensión en pantalla
const DURACION = 12;         // segundos por turno
const MAX_EMPUJES = 3, TURNOS = 6;   // 3 turnos por jugador
const R1 = 12, R2 = 18, RG = 22;     // radios (px): masa 1, masa 2 y bloque
const COLORES = ["#F2A33A", "#E0527F"];

/* ---------- 2. Física: ecuaciones de movimiento ---------- */
function aceleraciones(s) {
  const d = s.th1 - s.th2, den = 2*P.m1 + P.m2 - P.m2*Math.cos(2*d);
  const a1 = (-P.g*(2*P.m1 + P.m2)*Math.sin(s.th1) - P.m2*P.g*Math.sin(s.th1 - 2*s.th2)
            - 2*Math.sin(d)*P.m2*(s.w2*s.w2*P.L2 + s.w1*s.w1*P.L1*Math.cos(d))) / (P.L1*den);
  const a2 = (2*Math.sin(d)*(s.w1*s.w1*P.L1*(P.m1 + P.m2) + P.g*(P.m1 + P.m2)*Math.cos(s.th1)
            + s.w2*s.w2*P.L2*P.m2*Math.cos(d))) / (P.L2*den);
  return [a1, a2];
}
const deriv = y => { const [a1, a2] = aceleraciones({ th1: y[0], th2: y[1], w1: y[2], w2: y[3] }); return [y[2], y[3], a1, a2]; };
function rk4(s, h) {                       // un paso de Runge-Kutta de 4.º orden
  const y = [s.th1, s.th2, s.w1, s.w2];
  const mas = (y, k, c) => y.map((v, i) => v + c*k[i]);
  const k1 = deriv(y), k2 = deriv(mas(y, k1, h/2)), k3 = deriv(mas(y, k2, h/2)), k4 = deriv(mas(y, k3, h));
  const n = y.map((v, i) => v + h/6*(k1[i] + 2*k2[i] + 2*k3[i] + k4[i]));
  s.th1 = n[0]; s.th2 = n[1]; s.w1 = n[2]; s.w2 = n[3];
}
// Posición en pantalla de las dos masas
function posiciones(s) {
  const x1 = P.L1*Math.sin(s.th1), y1 = -P.L1*Math.cos(s.th1);
  const x2 = x1 + P.L2*Math.sin(s.th2), y2 = y1 - P.L2*Math.cos(s.th2);
  return { a: [PX + x1*ESC, PY - y1*ESC], b: [PX + x2*ESC, PY - y2*ESC] };
}

/* ---------- 3. Estado del juego ---------- */
const BLOQUES_BASE = [   // posición (m) respecto al punto de suspensión, color y puntos
  { x: -1.6, y: -0.7, color: "#E53935", pts: 10 }, { x: -1.0, y: -1.5, color: "#1E88E5", pts: 10 },
  { x: -0.45, y: -1.8, color: "#FFC107", pts: 30 }, { x: 0.5, y: -1.6, color: "#43A047", pts: 10 },
  { x: 1.2, y: -1.2, color: "#8E24AA", pts: 10 },   { x: 1.7, y: -0.5, color: "#FB8C00", pts: 10 },
  { x: -0.7, y: -1.0, color: "#EC407A", pts: 10 },   { x: -1.8, y: -0.2, color: "#00ACC1", pts: 10 },
  { x: 0.9, y: -0.3, color: "#7CB342", pts: 10 }
];
let fase = "config";         // config | preparar | volando | fin
let turno = 0, puntos = [0, 0], nombres = ["Jugador 1", "Jugador 2"];
let S = { th1: 0.3, th2: 0.3, w1: 0, w2: 0 };   // estado del péndulo
let bloques = [], particulas = [], estela = [];
let tRest = DURACION, empujes = 0, ptsTurno = 0, derribados = 0, arrastrando = false;
const jugador = () => turno % 2;

/* ---------- 4. Dibujo ---------- */
const fondo = (() => {        // la obra se dibuja una sola vez en un canvas aparte
  const c = document.createElement("canvas"); c.width = W; c.height = H;
  const x = c.getContext("2d"); x.lineCap = "round";
  x.fillStyle = "#9AD4F0"; x.fillRect(0, 0, W, H);                       // cielo
  x.fillStyle = "#FFE08A"; x.beginPath(); x.arc(820, 150, 36, 0, 7); x.fill();   // sol
  x.fillStyle = "#fff"; [[300, 50], [600, 40]].forEach(([a, b]) => { x.beginPath(); x.ellipse(a, b, 55, 18, 0, 0, 7); x.fill(); });
  x.fillStyle = "#8FA6B5";                                               // ciudad lejana
  [[520, 300, 60], [580, 250, 70], [650, 320, 50], [700, 280, 70], [770, 310, 60], [830, 270, 70]].forEach(([a, t, w]) => x.fillRect(a, t, w, 500 - t));
  x.strokeStyle = "#5d6d7a"; x.lineWidth = 6;                            // edificio en construcción
  [660, 740, 820].forEach(a => { x.beginPath(); x.moveTo(a, 340); x.lineTo(a, 500); x.stroke(); });
  [340, 400, 460].forEach(b => { x.beginPath(); x.moveTo(650, b); x.lineTo(830, b); x.stroke(); });
  x.lineWidth = 3; x.beginPath(); x.moveTo(660, 340); x.lineTo(740, 400); x.moveTo(740, 340); x.lineTo(660, 400); x.moveTo(740, 400); x.lineTo(820, 460); x.moveTo(820, 400); x.lineTo(740, 460); x.stroke();
  x.fillStyle = "#C49A62"; x.fillRect(0, 500, W, H - 500);               // tierra
  x.fillStyle = "#A97C45"; x.fillRect(0, 500, W, 10);
  for (let k = 0; k < W; k += 40) { x.fillStyle = (k/40) % 2 ? "#F2B705" : "#1d2a30"; x.fillRect(k, 548, 40, 12); }   // franja de seguridad
  x.fillStyle = "#1E88E5"; x.fillRect(90, 452, 100, 48);                 // contenedor
  x.strokeStyle = "#1565C0"; x.lineWidth = 3; for (let k = 100; k < 190; k += 14) { x.beginPath(); x.moveTo(k, 456); x.lineTo(k, 496); x.stroke(); }
  [[250, 500], [600, 500]].forEach(([a, b]) => {                         // conos
    x.fillStyle = "#FF6D00"; x.beginPath(); x.moveTo(a, b - 36); x.lineTo(a - 13, b); x.lineTo(a + 13, b); x.fill();
    x.fillStyle = "#fff"; x.fillRect(a - 8, b - 22, 16, 6);
  });
  x.strokeStyle = "#F2B705"; x.lineWidth = 5;                            // torre de la grúa
  [40, 72].forEach(a => { x.beginPath(); x.moveTo(a, 60); x.lineTo(a, 500); x.stroke(); });
  for (let y = 500; y > 96; y -= 36) { x.beginPath(); x.moveTo(40, y); x.lineTo(72, y - 36); x.moveTo(72, y); x.lineTo(40, y - 36); x.stroke(); }
  x.beginPath(); x.moveTo(20, 74); x.lineTo(830, 74); x.moveTo(20, 96); x.lineTo(830, 96); x.stroke();   // brazo (pluma)
  x.lineWidth = 3; x.beginPath(); for (let k = 20; k < 820; k += 30) { x.moveTo(k, 96); x.lineTo(k + 15, 74); x.lineTo(k + 30, 96); } x.stroke();
  x.strokeStyle = "#333"; x.lineWidth = 2; x.beginPath();                // tirantes
  x.moveTo(56, 18); x.lineTo(40, 60); x.moveTo(56, 18); x.lineTo(72, 60); x.moveTo(56, 18); x.lineTo(830, 74); x.moveTo(56, 18); x.lineTo(20, 74); x.stroke();
  x.fillStyle = "#555"; x.fillRect(20, 96, 30, 34);                      // contrapeso
  x.fillStyle = "#1d2a30"; x.fillRect(PX - 20, 92, 40, 12);              // carro de la grúa
  x.strokeStyle = "#333"; x.lineWidth = 4; x.beginPath(); x.moveTo(PX, 104); x.lineTo(PX, PY); x.stroke();
  return c;
})();

function dibujarBloque(b) {       // un bloque colgado con un cable de la pluma de la grúa
  const sx = PX + b.x*ESC, sy = PY - b.y*ESC;
  g.strokeStyle = "#333"; g.lineWidth = 2; g.beginPath(); g.moveTo(sx, 96); g.lineTo(sx, sy - 20); g.stroke();
  g.fillStyle = b.color; g.fillRect(sx - 20, sy - 20, 40, 40);
  g.strokeStyle = "rgba(0,0,0,.45)"; g.lineWidth = 3; g.strokeRect(sx - 20, sy - 20, 40, 40);
  g.beginPath(); g.moveTo(sx - 20, sy - 20); g.lineTo(sx + 20, sy + 20); g.moveTo(sx + 20, sy - 20); g.lineTo(sx - 20, sy + 20); g.stroke();
  if (b.pts > 10) {
    g.fillStyle = "#fff"; g.beginPath(); g.arc(sx, sy, 12, 0, 7); g.fill();
    g.fillStyle = "#1d2a30"; g.font = "bold 14px sans-serif"; g.textAlign = "center"; g.fillText(b.pts, sx, sy + 5);
  }
}
function dibujarTexto(t) {
  g.font = "bold 30px sans-serif"; g.textAlign = "center"; g.lineWidth = 6; g.strokeStyle = "#fff"; g.fillStyle = "#17301c";
  g.strokeText(t, W/2, 300); g.fillText(t, W/2, 300);
}
function dibujar() {
  g.drawImage(fondo, 0, 0);
  bloques.forEach(b => { if (b.vivo) dibujarBloque(b); });
  if (estela.length > 1) {                                       // estela de la bola
    for (let i = 1; i < estela.length; i++) {
      g.strokeStyle = `rgba(255,255,255,${(i/estela.length*0.8).toFixed(2)})`; g.lineWidth = 4;
      g.beginPath(); g.moveTo(...estela[i-1]); g.lineTo(...estela[i]); g.stroke();
    }
  }
  const p = posiciones(S);
  g.strokeStyle = "#2b2b2b"; g.lineWidth = 4; g.beginPath();                    // cable de acero
  g.moveTo(PX, PY); g.lineTo(...p.a); g.lineTo(...p.b); g.stroke();
  g.fillStyle = "#F2B705"; g.strokeStyle = "#1d2a30"; g.lineWidth = 3;           // bloque del gancho
  g.beginPath(); g.arc(...p.a, R1, 0, 7); g.fill(); g.stroke();
  g.fillStyle = "#3a3f44"; g.beginPath(); g.arc(...p.b, R2, 0, 7); g.fill();     // bola de demolición
  g.strokeStyle = COLORES[jugador()]; g.lineWidth = 5; g.beginPath(); g.arc(...p.b, R2 - 2, 0, 7); g.stroke();
  g.fillStyle = "rgba(255,255,255,.5)"; g.beginPath(); g.arc(p.b[0] - 6, p.b[1] - 6, 5, 0, 7); g.fill();
  particulas.forEach(q => { g.fillStyle = q.color; g.globalAlpha = Math.max(0, q.vida); g.fillRect(q.x, q.y, 6, 6); });
  g.globalAlpha = 1;
  if (fase === "preparar") dibujarTexto("Arrastra la bola y suéltala");
  if (fase === "config") dibujarTexto("Escribe los nombres y pulsa Comenzar");
}

/* ---------- 5. Interacción: arrastrar y soltar ---------- */
// Cinemática inversa (L1 = L2): calcula θ1 y θ2 para que la bola quede en (px, py)
function colocarPendulo(px, py) {
  const rx = (px - PX)/ESC, ry = (PY - py)/ESC;
  const d = Math.min(Math.max(Math.hypot(rx, ry), 0.15), 2*P.L1*0.999);
  const alfa = Math.acos(d/(2*P.L1)), fi = Math.atan2(rx, -ry);
  S = { th1: fi - alfa, th2: fi + alfa, w1: 0, w2: 0 };
}
function coordenadas(e) {
  const r = cv.getBoundingClientRect();
  return [(e.clientX - r.left)*W/r.width, (e.clientY - r.top)*H/r.height];
}
cv.addEventListener("pointerdown", e => {
  if (fase !== "preparar") return;
  arrastrando = true; cv.setPointerCapture(e.pointerId); cv.classList.add("arrastrando");
  colocarPendulo(...coordenadas(e)); dibujar();
});
cv.addEventListener("pointermove", e => { if (arrastrando) { colocarPendulo(...coordenadas(e)); dibujar(); } });
cv.addEventListener("pointerup", () => {
  if (!arrastrando) return;
  arrastrando = false; cv.classList.remove("arrastrando"); lanzar();
});

/* ---------- 6. Turnos y puntuación ---------- */
function actualizarPantalla() {
  [0, 1].forEach(i => {
    $("nom-" + (i+1)).textContent = nombres[i]; $("pts-" + (i+1)).textContent = puntos[i];
    $("tarj-" + (i+1)).classList.toggle("activa", fase !== "config" && fase !== "final" && jugador() === i);
  });
  const vuelo = fase === "volando";
  $("btn-izq").disabled = !vuelo || empujes <= 0; $("btn-der").disabled = !vuelo || empujes <= 0;
  $("empujes").textContent = "Empujones: " + empujes;
  $("tiempo").textContent = vuelo ? tRest.toFixed(1) + " s" : "";
}
function iniciarTurno() {
  fase = "preparar"; tRest = DURACION; empujes = MAX_EMPUJES; ptsTurno = 0; derribados = 0;
  bloques = BLOQUES_BASE.map(b => ({ ...b, vivo: true })); particulas = []; estela = [];
  S = { th1: 0.3, th2: 0.3, w1: 0, w2: 0 };
  $("btn-siguiente").hidden = true;
  $("estado").textContent = `Turno ${Math.floor(turno/2) + 1} de 3: ${nombres[jugador()]}`;
  actualizarPantalla(); dibujar();
}
function lanzar() {
  fase = "volando"; estela = [];
  $("estado").textContent = `${nombres[jugador()]}: ¡derriba bloques!`;
  actualizarPantalla();
}
function empujar(dir) {              // un empujón cambia la velocidad angular de la masa 1
  if (fase !== "volando" || empujes <= 0) return;
  S.w1 += dir*2; empujes--; actualizarPantalla();
}
function revisarGolpes() {
  const p = posiciones(S);
  bloques.forEach(b => {
    if (!b.vivo) return;
    const sx = PX + b.x*ESC, sy = PY - b.y*ESC;
    if (Math.hypot(sx - p.b[0], sy - p.b[1]) < R2 + RG || Math.hypot(sx - p.a[0], sy - p.a[1]) < R1 + RG) {
      b.vivo = false; derribados++; ptsTurno += b.pts; puntos[jugador()] += b.pts;
      for (let i = 0; i < 12; i++) {
        const a = Math.random()*6.28, v = 60 + Math.random()*120;
        particulas.push({ x: sx, y: sy, vx: Math.cos(a)*v, vy: Math.sin(a)*v, vida: 1, color: b.color });
      }
    }
  });
}
function finTurno() {
  fase = "fin";
  $("estado").textContent = `${nombres[jugador()]}: ${derribados} bloques, +${ptsTurno} pts`;
  $("btn-siguiente").textContent = turno + 1 < TURNOS ? "Siguiente turno" : "Ver resultado final";
  $("btn-siguiente").hidden = false; actualizarPantalla();
}
function finalizar() {
  fase = "final"; const [a, b] = puntos;
  $("banner").classList.toggle("empate", a === b);
  if (a === b) { $("banner-texto").textContent = "¡EMPATE!"; $("banner-sub").textContent = `${a} puntos para cada jugador`; }
  else {
    const gan = a > b ? 0 : 1;
    $("banner-texto").textContent = "¡GANASTE!";
    $("banner-sub").textContent = `${nombres[gan]} gana con ${puntos[gan]} puntos (${nombres[1-gan]}: ${puntos[1-gan]})`;
    $("tarj-" + (gan+1)).classList.add("ganador");
  }
  $("banner").hidden = false; $("btn-siguiente").hidden = true;
  $("estado").textContent = "Fin del juego"; actualizarPantalla();
}
function comenzar() {
  const nom = (id, d) => ($(id).value.trim() || d).slice(0, 20);
  nombres = [nom("j-nombre1", "Jugador 1"), nom("j-nombre2", "Jugador 2")];
  puntos = [0, 0]; turno = 0; $("banner").hidden = true;
  $("tarj-1").classList.remove("ganador"); $("tarj-2").classList.remove("ganador");
  $("config").hidden = true; iniciarTurno();
}
function reiniciarJuego() {
  fase = "config"; puntos = [0, 0]; turno = 0; bloques = []; particulas = []; estela = [];
  S = { th1: 0.3, th2: 0.3, w1: 0, w2: 0 };
  $("banner").hidden = true; $("config").hidden = false; $("btn-siguiente").hidden = true;
  $("tarj-1").classList.remove("ganador"); $("tarj-2").classList.remove("ganador");
  $("estado").textContent = "Escribe los nombres y pulsa Comenzar.";
  actualizarPantalla(); dibujar();
}

/* ---------- 7. Bucle de animación ---------- */
let ultimo = null;
function bucle(ts) {
  const dt = ultimo === null ? 0.016 : Math.min((ts - ultimo)/1000, 0.033);
  ultimo = ts;
  if (fase === "volando") {
    const n = Math.max(1, Math.round(dt/DT));
    for (let i = 0; i < n; i++) rk4(S, DT);
    tRest -= n*DT;
    if (![S.th1, S.th2, S.w1, S.w2].every(Number.isFinite)) S = { th1: 0.3, th2: 0.3, w1: 0, w2: 0 };   // protección
    estela.push(posiciones(S).b); if (estela.length > 40) estela.shift();
    revisarGolpes(); actualizarPantalla();
    if (tRest <= 0 || bloques.every(b => !b.vivo)) finTurno();
  }
  particulas.forEach(q => { q.x += q.vx*dt; q.y += q.vy*dt; q.vy += 300*dt; q.vida -= dt*1.2; });
  particulas = particulas.filter(q => q.vida > 0);
  if (fase !== "preparar" || !arrastrando) dibujar();
  requestAnimationFrame(bucle);
}

/* ---------- 8. Eventos y arranque ---------- */
$("btn-comenzar").addEventListener("click", comenzar);
$("btn-reiniciar").addEventListener("click", reiniciarJuego);
$("btn-izq").addEventListener("click", () => empujar(-1));
$("btn-der").addEventListener("click", () => empujar(1));
$("btn-siguiente").addEventListener("click", () => { turno++; turno < TURNOS ? iniciarTurno() : finalizar(); });
document.addEventListener("keydown", e => {
  if (e.target.tagName === "INPUT") return;
  if (e.key === "ArrowLeft") empujar(-1); if (e.key === "ArrowRight") empujar(1);
});
actualizarPantalla();
requestAnimationFrame(bucle);
