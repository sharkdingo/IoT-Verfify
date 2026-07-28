import type { RouteLocationNormalizedLoaded, RouteLocationRaw } from 'vue-router';
import { router } from './index';

/**
 * Single owner of the "session is gone, go to the login surface" location shape.
 *
 * Returns `null` when the caller is already on the public login surface, so no caller
 * has to re-implement that check. Kept router-instance free so component callers can
 * navigate with their own injected router.
 */
export const loginRedirectTarget = (
  current: Pick<RouteLocationNormalizedLoaded, 'path' | 'fullPath'>
): RouteLocationRaw | null => {
  if (current.path === '/') return null;

  const query: Record<string, string> = { mode: 'login' };
  if (current.fullPath && current.fullPath !== '/') {
    query.redirect = current.fullPath;
  }
  return { path: '/', query };
};

/** For non-component callers (axios interceptor, SSE transport) that only have the singleton. */
export const redirectToLogin = async (options: { replace?: boolean } = {}): Promise<void> => {
  const target = loginRedirectTarget(router.currentRoute.value);
  if (!target) return;
  await (options.replace ? router.replace(target) : router.push(target));
};
