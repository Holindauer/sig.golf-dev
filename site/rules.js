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
function flashReference(target) {
  const marker = target.matches('.rule-section, .program-block')
    ? target.querySelector('h2, h3') : target;
  if (!marker) return;
  marker.classList.remove('rule-ref-flash');
  void marker.offsetWidth;
  marker.classList.add('rule-ref-flash');
  clearTimeout(flashTimers.get(marker));
  flashTimers.set(marker, setTimeout(() => marker.classList.remove('rule-ref-flash'), 2000));
}
document.addEventListener('click', event => {
  const link = event.target.closest('a[href^="#"]');
  if (!link) return;
  const target = document.getElementById(link.dataset.highlight || link.hash.slice(1));
  if (target) flashReference(target);
});
