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
