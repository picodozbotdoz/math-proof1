// Hover/focus tooltips for chart marks carrying data-tip.  No network, no storage.
(function () {
  var tip = document.createElement("div");
  tip.id = "tip";
  document.body.appendChild(tip);
  function show(e) {
    var t = e.target.closest && e.target.closest("[data-tip]");
    if (!t) { tip.style.display = "none"; return; }
    tip.textContent = t.getAttribute("data-tip");
    tip.style.display = "block";
    var r = t.getBoundingClientRect();
    var x = e.clientX !== undefined && e.type !== "focusin" ? e.clientX : r.left + r.width / 2;
    var y = e.clientY !== undefined && e.type !== "focusin" ? e.clientY : r.top;
    tip.style.left = Math.max(6, Math.min(x + 12, innerWidth - tip.offsetWidth - 6)) + "px";
    tip.style.top = Math.max(6, y - tip.offsetHeight - 10) + "px";
  }
  document.addEventListener("mousemove", show);
  document.addEventListener("focusin", show);
  document.addEventListener("focusout", function () { tip.style.display = "none"; });
})();
