'use strict';

const sectionLinks = [...document.querySelectorAll('.rules-toc a[href^="#"]')];
const sections = sectionLinks.map(link => document.querySelector(link.getAttribute('href')));
let scheduled = false;
function updateCurrentSection() {
  scheduled = false;
  const threshold = 120;
  let current = 0;
  for (let index = 0; index < sections.length; index++) {
    if (sections[index].getBoundingClientRect().top <= threshold) current = index;
  }
  sectionLinks.forEach((link, index) => {
    if (index === current) link.setAttribute('aria-current', 'location');
    else link.removeAttribute('aria-current');
  });
}
function scheduleSectionUpdate() {
  if (!scheduled) {
    scheduled = true;
    requestAnimationFrame(updateCurrentSection);
  }
}
addEventListener('scroll', scheduleSectionUpdate, {passive: true});
addEventListener('resize', scheduleSectionUpdate);
addEventListener('hashchange', scheduleSectionUpdate);
updateCurrentSection();

const flashTimers = new WeakMap();
let pendingReference = 0;
function flashReference(marker) {
  marker.classList.remove('rule-ref-flash');
  void marker.offsetWidth;
  marker.classList.add('rule-ref-flash');
  clearTimeout(flashTimers.get(marker));
  flashTimers.set(marker, setTimeout(() => marker.classList.remove('rule-ref-flash'), 1000));
}
function revealReference(target) {
  const marker = target.matches('.rule-section, .program-block')
    ? target.querySelector('h2, h3') : target;
  if (!marker) return;
  const request = ++pendingReference;
  const initial = marker.getBoundingClientRect();
  if (initial.top >= innerHeight * .2 && initial.bottom <= innerHeight * .8) {
    flashReference(marker);
    return;
  }
  let lastTop = NaN;
  let stableFrames = 0;
  const deadline = performance.now() + 10000;
  function waitForArrival() {
    if (request !== pendingReference) return;
    const rect = marker.getBoundingClientRect();
    const visible = rect.top >= 0 && rect.bottom <= innerHeight;
    stableFrames = visible && Math.abs(rect.top - lastTop) < .5 ? stableFrames + 1 : 0;
    lastTop = rect.top;
    if (stableFrames >= 5) flashReference(marker);
    else if (performance.now() < deadline) requestAnimationFrame(waitForArrival);
  }
  requestAnimationFrame(waitForArrival);
}
document.addEventListener('click', event => {
  const link = event.target.closest('a[href^="#"]');
  if (!link) return;
  const target = document.getElementById(link.hash.slice(1));
  if (target) revealReference(target);
});
