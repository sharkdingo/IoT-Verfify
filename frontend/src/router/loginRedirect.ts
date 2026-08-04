import type { RouteLocationNormalizedLoaded, RouteLocationRaw } from 'vue-router';
import { router } from './index';

/**
 * Single owner of the "session is gone, go to the login surface" location shape.
 *
 * Returns `null` when the caller is already on the public login surface, so no caller
 * has to re-implement that check. Kept router-instance free so component callers can
 * navigate with their own injected router.
 */
/**
 * Why the user is being sent to the login surface.
 *
 * The caller knows this and the helper cannot infer it: a rejected token and a deliberate sign-out in another
 * tab produce the same navigation but mean opposite things. I first set `session-expired` inside this function
 * for every caller, and `App.spec.ts` caught it — that path is a *cross-tab logout*, where the user chose to
 * leave, so telling them their session expired would be a plain untruth.
 */
export type LoginRedirectReason = 'session-expired';

export const loginRedirectTarget = (
  current: Pick<RouteLocationNormalizedLoaded, 'path' | 'fullPath'>,
  reason?: LoginRedirectReason
): RouteLocationRaw | null => {
  if (current.path === '/') return null;

  const query: Record<string, string> = { mode: 'login' };
  if (current.fullPath && current.fullPath !== '/') {
    query.redirect = current.fullPath;
    // Only stated when the caller says so, and only alongside a return path — a `reason` without somewhere to
    // return to would be describing a session the user never had.
    if (reason) query.reason = reason;
  }
  return { path: '/', query };
};

/**
 * For non-component callers (axios interceptor, SSE transport) that only have the singleton.
 *
 * Both of those callers reach here because a token was rejected mid-request, so `session-expired` is the default
 * — it is the only reason they ever have. A component caller with a different reason passes it explicitly.
 */
export const redirectToLogin = async (
  options: { replace?: boolean, reason?: LoginRedirectReason } = {}
): Promise<void> => {
  const target = loginRedirectTarget(router.currentRoute.value, options.reason ?? 'session-expired');
  if (!target) return;
  await (options.replace ? router.replace(target) : router.push(target));
};
