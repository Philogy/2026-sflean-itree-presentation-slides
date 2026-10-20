// Click-stepped highlighting for `.stepped` slides: each `.fragment.step` names a step;
// code lines (tagged via `data-lines`) and diagram parts (`data-s`) of that step stay lit, the rest dims.
// Also restarts the SMIL animation of `img.fuel-anim` whenever its fragment is revealed.
(() => {
  const splitLines = box => {
    const code = box.querySelector('code[data-lines]');
    if (!code || code.dataset.split) return;
    const tags = code.dataset.lines.split('|');
    code.innerHTML = code.innerHTML.replace(/^\n|\n$/g, '').split('\n')
      .map((l, i) => `<span class="ln" data-s="${tags[i] || ''}">${l || ' '}</span>`).join('');
    code.dataset.split = '1';
  };
  const update = () => {
    for (const box of document.querySelectorAll('.stepped')) {
      splitLines(box);
      const shown = box.querySelectorAll('.fragment.step.visible');
      const step = shown.length ? shown[shown.length - 1].dataset.step : null;
      for (const el of box.querySelectorAll('[data-s]')) {
        const on = step && el.dataset.s.split(' ').includes(step);
        el.classList.toggle('step-on', !!on);
        el.classList.toggle('step-dim', !!step && !on);
      }
    }
  };
  const init = () => {
    ['fragmentshown', 'fragmenthidden', 'slidechanged'].forEach(e => Reveal.on(e, update));
    Reveal.on('fragmentshown', e => {
      const img = e.fragment.matches('img.fuel-anim') ? e.fragment : e.fragment.querySelector('img.fuel-anim');
      if (img) img.src = img.src.replace(/\?.*$/, '') + '?t=' + Date.now();
    });
    update();
  };
  Reveal.isReady() ? init() : Reveal.on('ready', init);
})();
